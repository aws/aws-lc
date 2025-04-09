(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/equiv.ml";;
needs "arm/proofs/neon_helper.ml";;

(* ========================================================================= *)
(* Montgomery squaring modulo p_256.                                         *)
(* ========================================================================= *)

(**** print_literal_from_elf "arm/p256/unopt/bignum_montsqr_p256_base.o";;
 ****)

let bignum_montsqr_p256_unopt_mc =
  define_assert_from_elf "bignum_montsqr_p256_unopt_mc" "arm/p256/unopt/bignum_montsqr_p256_base.o"
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
  0xeb0c01ed;       (* arm_SUBS X13 X15 X12 *)
  0xd360fdeb;       (* arm_LSR X11 X15 32 *)
  0xda0b01ef;       (* arm_SBC X15 X15 X11 *)
  0xab0c0210;       (* arm_ADDS X16 X16 X12 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0xba0d0021;       (* arm_ADCS X1 X1 X13 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xd3607e0c;       (* arm_LSL X12 X16 32 *)
  0xeb0c020d;       (* arm_SUBS X13 X16 X12 *)
  0xd360fe0b;       (* arm_LSR X11 X16 32 *)
  0xda0b0210;       (* arm_SBC X16 X16 X11 *)
  0xab0c0231;       (* arm_ADDS X17 X17 X12 *)
  0xba0b0021;       (* arm_ADCS X1 X1 X11 *)
  0xba0d01ef;       (* arm_ADCS X15 X15 X13 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
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
  0xeb0c00cd;       (* arm_SUBS X13 X6 X12 *)
  0xd360fccb;       (* arm_LSR X11 X6 32 *)
  0xda0b00c6;       (* arm_SBC X6 X6 X11 *)
  0xab0c00e7;       (* arm_ADDS X7 X7 X12 *)
  0xba0b0108;       (* arm_ADCS X8 X8 X11 *)
  0xba0d0129;       (* arm_ADCS X9 X9 X13 *)
  0xba06014a;       (* arm_ADCS X10 X10 X6 *)
  0x9a1f03e6;       (* arm_ADC X6 XZR XZR *)
  0xd3607cec;       (* arm_LSL X12 X7 32 *)
  0xeb0c00ed;       (* arm_SUBS X13 X7 X12 *)
  0xd360fceb;       (* arm_LSR X11 X7 32 *)
  0xda0b00e7;       (* arm_SBC X7 X7 X11 *)
  0xab0c0108;       (* arm_ADDS X8 X8 X12 *)
  0xba0b0129;       (* arm_ADCS X9 X9 X11 *)
  0xba0d014a;       (* arm_ADCS X10 X10 X13 *)
  0xba0700c6;       (* arm_ADCS X6 X6 X7 *)
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
  0xb2407feb;       (* arm_MOV X11 (rvalue (word 4294967295)) *)
  0xb1000505;       (* arm_ADDS X5 X8 (rvalue (word 1)) *)
  0xfa0b012b;       (* arm_SBCS X11 X9 X11 *)
  0xb26083ed;       (* arm_MOV X13 (rvalue (word 18446744069414584321)) *)
  0xfa1f014c;       (* arm_SBCS X12 X10 XZR *)
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

let BIGNUM_MONTSQR_P256_UNOPT_EXEC = ARM_MK_EXEC_RULE bignum_montsqr_p256_unopt_mc;;

(* bignum_montsqr_p256_unopt_mc without ret. *)
let bignum_montsqr_p256_unopt_core_mc_def,
    bignum_montsqr_p256_unopt_core_mc,
    BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC =
  mk_sublist_of_mc "bignum_montsqr_p256_unopt_core_mc"
    bignum_montsqr_p256_unopt_mc
    (`0`,`LENGTH bignum_montsqr_p256_unopt_mc - 4`)
    (fst BIGNUM_MONTSQR_P256_UNOPT_EXEC);;

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

let p_256 = new_definition `p_256 = 115792089210356248762697446949407573530086143415290314195533631308867097853951`;;

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

let BIGNUM_MONTSQR_P256_UNOPT_CORE_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p256_unopt_core_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p256_unopt_core_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + LENGTH bignum_montsqr_p256_unopt_core_mc) /\
                  (a EXP 2 <= 2 EXP 256 * p_256
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256 (2 EXP 256) * a EXP 2) MOD p_256))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a EXP 2 <= 2 EXP 256 * p_256  assumption ***)

  ASM_CASES_TAC `a EXP 2 <= 2 EXP 256 * p_256` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC (1--124)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  (*** Squaring and Montgomery reduction of lower half ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC
   [7;9;14;16;18;19;20;21;22;23;24;
    25;26;27;28;29;30;31;32;33;34;35;36;37;38;39;40]
   (1--40) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [VAL_WORD_MADDL_0; DIVMOD_33_31; VAL_WORD_USHR;
    VAL_WORD_SHL; DIMINDEX_64]) THEN
  SUBGOAL_THEN
   `2 EXP 128 * bignum_of_wordlist [sum_s37; sum_s38; sum_s39; sum_s40] =
    bignum_of_wordlist[x_0;x_1] EXP 2 +
    p_256 * bignum_of_wordlist[sum_s7; sum_s29]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; p_256; GSYM REAL_OF_NUM_CLAUSES] THEN
    MAP_EVERY (SUBST_ALL_TAC o SYM o C SPEC VAL_WORD_SPLIT32)
     [`x_0:int64`; `x_1:int64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV]) THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** ADK cross-product ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC (66--111) (66--111) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
        [sum_s95; sum_s108; sum_s109; sum_s110; sum_s111]` THEN
  SUBGOAL_THEN
   `t < 2 * p_256 /\ (2 EXP 256 * t == a EXP 2) (mod p_256)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `2 EXP 256 * t =
      a EXP 2 +
      p_256 * bignum_of_wordlist [sum_s7; sum_s29; sum_s71; sum_s80]`
    ASSUME_TAC THENL
     [TRANS_TAC EQ_TRANS
       `(bignum_of_wordlist[x_0;x_1] EXP 2 +
         p_256 * bignum_of_wordlist[sum_s7; sum_s29]) +
        2 * 2 EXP 128 *
            bignum_of_wordlist[x_0;x_1] * bignum_of_wordlist[x_2;x_3] +
        2 EXP 256 * bignum_of_wordlist[x_2;x_3] EXP 2 +
        2 EXP 128 * p_256 * bignum_of_wordlist [sum_s71; sum_s80]` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
        FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV o
                           RAND_CONV o RAND_CONV) [SYM th]);
        EXPAND_TAC "a" THEN REWRITE_TAC[bignum_of_wordlist] THEN
        ARITH_TAC] THEN
      EXPAND_TAC "t" THEN
      REWRITE_TAC[bignum_of_wordlist; p_256; GSYM REAL_OF_NUM_CLAUSES] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;

      ASM_REWRITE_TAC[NUMBER_RULE `(x + p * n:num == x) (mod p)`] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 256 * p
         ==> 2 EXP 256 * t < ab + 2 EXP 256 * p ==> t < 2 * p`)) THEN
      ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_256] THEN
      BOUNDER_TAC[]];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word_subword a b = c`]] THEN

  (*** Final correction stage ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC
   [113;114;116;117;118] (112--124) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM WORD_BITVAL; COND_SWAP; REAL_BITVAL_NOT]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_256` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a EXP 2) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a EXP 2) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`256`; `if t < p_256 then &t:real else &t - &p_256`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_CASES] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT]] THEN
  SUBGOAL_THEN `carry_s118 <=> t < p_256` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `320` THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[p_256; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD_BITVAL] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_256] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_MONTSQR_P256_UNOPT_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p256_unopt_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p256_unopt_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + LENGTH bignum_montsqr_p256_unopt_core_mc) /\
                  (a EXP 2 <= 2 EXP 256 * p_256
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256 (2 EXP 256) * a EXP 2) MOD p_256))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_MONTSQR_P256_UNOPT_CORE_CORRECT
    bignum_montsqr_p256_unopt_core_mc_def
    [fst BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC;
     fst BIGNUM_MONTSQR_P256_UNOPT_EXEC]);;

(* ------------------------------------------------------------------------- *)
(* Show that it also works as "almost-Montgomery" if desired. That is, even  *)
(* without the further range assumption on inputs we still get a congruence. *)
(* But the output, still 256 bits, may then not be fully reduced mod p_256.  *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_AMONTSQR_P256_UNOPT_CORE_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p256_unopt_core_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p256_unopt_core_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + LENGTH bignum_montsqr_p256_unopt_core_mc) /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_256 (2 EXP 256) * a EXP 2) (mod p_256))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  (*** Squaring and Montgomery reduction of lower half ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC
   [7;9;14;16;18;19;20;21;22;23;24;
    25;26;27;28;29;30;31;32;33;34;35;36;37;38;39;40]
   (1--40) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [VAL_WORD_MADDL_0; DIVMOD_33_31; VAL_WORD_USHR;
    VAL_WORD_SHL; DIMINDEX_64]) THEN
  SUBGOAL_THEN
   `2 EXP 128 * bignum_of_wordlist [sum_s37; sum_s38; sum_s39; sum_s40] =
    bignum_of_wordlist[x_0;x_1] EXP 2 +
    p_256 * bignum_of_wordlist[sum_s7; sum_s29]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; p_256; GSYM REAL_OF_NUM_CLAUSES] THEN
    MAP_EVERY (SUBST_ALL_TAC o SYM o C SPEC VAL_WORD_SPLIT32)
     [`x_0:int64`; `x_1:int64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV]) THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** ADK cross-product ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC (66--111) (66--111) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
        [sum_s95; sum_s108; sum_s109; sum_s110; sum_s111]` THEN
  SUBGOAL_THEN
   `t < 2 EXP 256 + p_256 /\ (2 EXP 256 * t == a EXP 2) (mod p_256)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `2 EXP 256 * t =
      a EXP 2 +
      p_256 * bignum_of_wordlist [sum_s7; sum_s29; sum_s71; sum_s80]`
    ASSUME_TAC THENL
     [TRANS_TAC EQ_TRANS
       `(bignum_of_wordlist[x_0;x_1] EXP 2 +
         p_256 * bignum_of_wordlist[sum_s7; sum_s29]) +
        2 * 2 EXP 128 *
            bignum_of_wordlist[x_0;x_1] * bignum_of_wordlist[x_2;x_3] +
        2 EXP 256 * bignum_of_wordlist[x_2;x_3] EXP 2 +
        2 EXP 128 * p_256 * bignum_of_wordlist [sum_s71; sum_s80]` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
        FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV o
                           RAND_CONV o RAND_CONV) [SYM th]);
        EXPAND_TAC "a" THEN REWRITE_TAC[bignum_of_wordlist] THEN
        ARITH_TAC] THEN
      EXPAND_TAC "t" THEN
      REWRITE_TAC[bignum_of_wordlist; p_256; GSYM REAL_OF_NUM_CLAUSES] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;

      ASM_REWRITE_TAC[NUMBER_RULE `(x + p * n:num == x) (mod p)`] THEN
      MATCH_MP_TAC(ARITH_RULE `2 EXP 256 * x < 2 EXP 256 * y ==> x < y`) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "a" THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_256] THEN
      BOUNDER_TAC[]];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word_subword a b = c`]] THEN

  (*** Final correction ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC
   [113;114;116;117;118] (112--124) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM WORD_BITVAL; COND_SWAP; REAL_BITVAL_NOT]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `carry_s118 <=> t < p_256` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `320` THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_256] THEN
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
   [REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  MATCH_MP_TAC(NUMBER_RULE `!b:num. x + b * p = y ==> (x == y) (mod p)`) THEN
  EXISTS_TAC `bitval(p_256 <= t)` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a + b:real = c <=> c - b = a`] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN CONJ_TAC THENL
   [UNDISCH_TAC `t < 2 EXP 256 + p_256` THEN
    REWRITE_TAC[bitval; p_256; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
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
  REWRITE_TAC[BITVAL_CLAUSES; p_256] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REAL_INTEGER_TAC);;

let BIGNUM_AMONTSQR_P256_UNOPT_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p256_unopt_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p256_unopt_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + LENGTH bignum_montsqr_p256_unopt_core_mc) /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_256 (2 EXP 256) * a EXP 2) (mod p_256))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_AMONTSQR_P256_UNOPT_CORE_CORRECT
    bignum_montsqr_p256_unopt_core_mc_def
    [fst BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC;fst BIGNUM_MONTSQR_P256_UNOPT_EXEC]);;



(******************************************************************************
  The first program equivalence between the source program and
  its SIMD-vectorized but not instruction-scheduled program
******************************************************************************)

(* This is the intermediate program that is equivalent to both
   bignum_montsqr_p256_base and bignum_montsqr_p256. This is a vectorized
   version of bignum_montsqr_p256_base but instructions are unscheduled. *)

let bignum_montsqr_p256_interm1_ops:int list = [
    0xa9400c27; (* ldp      x7, x3, [x1] *)
    0x3dc00026; (* ldr      q6, [x1] *)
    0xa9412029; (* ldp      x9, x8, [x1, #16] *)
    0x3dc00432; (* ldr      q18, [x1, #16] *)
    0x3dc0003b; (* ldr      q27, [x1] *)
    0x2ebbc370; (* umull    v16.2d, v27.2s, v27.2s *)
    0x6ebbc371; (* umull2   v17.2d, v27.4s, v27.4s *)
    0x0ea12b7e; (* xtn      v30.2s, v27.2d *)
    0x4e9b5b7b; (* uzp2     v27.4s, v27.4s, v27.4s *)
    0x2ebec37b; (* umull    v27.2d, v27.2s, v30.2s *)
    0x4e083e06; (* mov      x6, v16.d[0] *)
    0x4e183e0c; (* mov      x12, v16.d[1] *)
    0x4e083e2d; (* mov      x13, v17.d[0] *)
    0x4e183e21; (* mov      x1, v17.d[1] *)
    0x4e083f6f; (* mov      x15, v27.d[0] *)
    0x4e183f6a; (* mov      x10, v27.d[1] *)
    0xab0f84c4; (* adds     x4, x6, x15, lsl #33 *)
    0xd35ffde6; (* lsr      x6, x15, #31 *)
    0x9a06018f; (* adc      x15, x12, x6 *)
    0xab0a85ad; (* adds     x13, x13, x10, lsl #33 *)
    0xd35ffd46; (* lsr      x6, x10, #31 *)
    0x9a06002c; (* adc      x12, x1, x6 *)
    0x9b037ce6; (* mul      x6, x7, x3 *)
    0x9bc37ce1; (* umulh    x1, x7, x3 *)
    0xab0605e5; (* adds     x5, x15, x6, lsl #1 *)
    0x93c6fc26; (* extr     x6, x1, x6, #63 *)
    0xba0601aa; (* adcs     x10, x13, x6 *)
    0xd37ffc26; (* lsr      x6, x1, #63 *)
    0x9a06018f; (* adc      x15, x12, x6 *)
    0xd3607c86; (* lsl      x6, x4, #32 *)
    0xeb06008d; (* subs     x13, x4, x6 *)
    0xd360fc8c; (* lsr      x12, x4, #32 *)
    0xda0c0081; (* sbc      x1, x4, x12 *)
    0xab0600a6; (* adds     x6, x5, x6 *)
    0xba0c0145; (* adcs     x5, x10, x12 *)
    0xba0d01ea; (* adcs     x10, x15, x13 *)
    0x9a1f002f; (* adc      x15, x1, xzr *)
    0xd3607ccd; (* lsl      x13, x6, #32 *)
    0xeb0d00cc; (* subs     x12, x6, x13 *)
    0xd360fcc1; (* lsr      x1, x6, #32 *)
    0xda0100c6; (* sbc      x6, x6, x1 *)
    0xab0d00b0; (* adds     x16, x5, x13 *)
    0xba01014b; (* adcs     x11, x10, x1 *)
    0xba0c01e2; (* adcs     x2, x15, x12 *)
    0x9a1f00d1; (* adc      x17, x6, xzr *)
    0x4e861a5e; (* uzp1     v30.4s, v18.4s, v6.4s *)
    0x4ea00a5b; (* rev64    v27.4s, v18.4s *)
    0x4e8618d2; (* uzp1     v18.4s, v6.4s, v6.4s *)
    0x4ea69f7b; (* mul      v27.4s, v27.4s, v6.4s *)
    0x6ea02b65; (* uaddlp   v5.2d, v27.4s *)
    0x4f6054a6; (* shl      v6.2d, v5.2d, #32 *)
    0x2ebe8246; (* umlal    v6.2d, v18.2s, v30.2s *)
    0x4e083cc4; (* mov      x4, v6.d[0] *)
    0x4e183cc5; (* mov      x5, v6.d[1] *)
    0x9bc97cea; (* umulh    x10, x7, x9 *)
    0xeb0300e6; (* subs     x6, x7, x3 *)
    0xda8624cd; (* cneg     x13, x6, cc  // cc = lo, ul, last *)
    0xda9f23ec; (* csetm    x12, cc  // cc = lo, ul, last *)
    0xeb090106; (* subs     x6, x8, x9 *)
    0xda8624c6; (* cneg     x6, x6, cc  // cc = lo, ul, last *)
    0x9b067da1; (* mul      x1, x13, x6 *)
    0x9bc67da6; (* umulh    x6, x13, x6 *)
    0xda8c218f; (* cinv     x15, x12, cc  // cc = lo, ul, last *)
    0xca0f002c; (* eor      x12, x1, x15 *)
    0xca0f00cd; (* eor      x13, x6, x15 *)
    0xab0a0081; (* adds     x1, x4, x10 *)
    0x9a1f0146; (* adc      x6, x10, xzr *)
    0x9bc87c63; (* umulh    x3, x3, x8 *)
    0xab050021; (* adds     x1, x1, x5 *)
    0xba0300c6; (* adcs     x6, x6, x3 *)
    0x9a1f0063; (* adc      x3, x3, xzr *)
    0xab0500c6; (* adds     x6, x6, x5 *)
    0x9a1f0063; (* adc      x3, x3, xzr *)
    0xb10005ff; (* cmn      x15, #0x1 *)
    0xba0c002c; (* adcs     x12, x1, x12 *)
    0xba0d00c1; (* adcs     x1, x6, x13 *)
    0x9a0f0063; (* adc      x3, x3, x15 *)
    0xab040086; (* adds     x6, x4, x4 *)
    0xba0c018d; (* adcs     x13, x12, x12 *)
    0xba01002c; (* adcs     x12, x1, x1 *)
    0xba030061; (* adcs     x1, x3, x3 *)
    0x9a1f03e3; (* adc      x3, xzr, xzr *)
    0xab1000c6; (* adds     x6, x6, x16 *)
    0xba0b01a5; (* adcs     x5, x13, x11 *)
    0xba02018a; (* adcs     x10, x12, x2 *)
    0xba11002f; (* adcs     x15, x1, x17 *)
    0x9a1f006d; (* adc      x13, x3, xzr *)
    0xd3607cc3; (* lsl      x3, x6, #32 *)
    0xeb0300cc; (* subs     x12, x6, x3 *)
    0xd360fcc1; (* lsr      x1, x6, #32 *)
    0xda0100c6; (* sbc      x6, x6, x1 *)
    0xab0300a3; (* adds     x3, x5, x3 *)
    0xba010145; (* adcs     x5, x10, x1 *)
    0xba0c01ef; (* adcs     x15, x15, x12 *)
    0xba0601ad; (* adcs     x13, x13, x6 *)
    0x9a1f03ea; (* adc      x10, xzr, xzr *)
    0xd3607c66; (* lsl      x6, x3, #32 *)
    0xeb06006c; (* subs     x12, x3, x6 *)
    0xd360fc61; (* lsr      x1, x3, #32 *)
    0xda010063; (* sbc      x3, x3, x1 *)
    0xab0600a6; (* adds     x6, x5, x6 *)
    0xba0101ef; (* adcs     x15, x15, x1 *)
    0xba0c01ad; (* adcs     x13, x13, x12 *)
    0xba03014c; (* adcs     x12, x10, x3 *)
    0x9a1f03e1; (* adc      x1, xzr, xzr *)
    0x9b097d23; (* mul      x3, x9, x9 *)
    0xab0300c5; (* adds     x5, x6, x3 *)
    0x9b087d06; (* mul      x6, x8, x8 *)
    0x9bc97d23; (* umulh    x3, x9, x9 *)
    0xba0301ef; (* adcs     x15, x15, x3 *)
    0xba0601ad; (* adcs     x13, x13, x6 *)
    0x9bc87d03; (* umulh    x3, x8, x8 *)
    0xba03018c; (* adcs     x12, x12, x3 *)
    0x9a1f0021; (* adc      x1, x1, xzr *)
    0x9b087d26; (* mul      x6, x9, x8 *)
    0x9bc87d23; (* umulh    x3, x9, x8 *)
    0xab0600c8; (* adds     x8, x6, x6 *)
    0xba030069; (* adcs     x9, x3, x3 *)
    0x9a1f03e3; (* adc      x3, xzr, xzr *)
    0xab0801ea; (* adds     x10, x15, x8 *)
    0xba0901af; (* adcs     x15, x13, x9 *)
    0xba03018d; (* adcs     x13, x12, x3 *)
    0xba1f002c; (* adcs     x12, x1, xzr *)
    0xb2407fe3; (* mov      x3, #0xffffffff                 // #4294967295 *)
    0xb10004a6; (* adds     x6, x5, #0x1 *)
    0xfa030148; (* sbcs     x8, x10, x3 *)
    0xb26083e3; (* mov      x3, #0xffffffff00000001         // #-4294967295 *)
    0xfa1f01e9; (* sbcs     x9, x15, xzr *)
    0xfa0301a1; (* sbcs     x1, x13, x3 *)
    0xfa1f019f; (* sbcs     xzr, x12, xzr *)
    0x9a8520c6; (* csel     x6, x6, x5, cs  // cs = hs, nlast *)
    0x9a8a2108; (* csel     x8, x8, x10, cs  // cs = hs, nlast *)
    0x9a8f2129; (* csel     x9, x9, x15, cs  // cs = hs, nlast *)
    0x9a8d2023; (* csel     x3, x1, x13, cs  // cs = hs, nlast *)
    0xa9002006; (* stp      x6, x8, [x0] *)
    0xa9010c09; (* stp      x9, x3, [x0, #16] *)
    0xd65f03c0; (* ret *)
];;

let bignum_montsqr_p256_interm1_mc =
  define_mc_from_intlist "bignum_montsqr_p256_interm1_mc" bignum_montsqr_p256_interm1_ops;;

let BIGNUM_MONTSQR_P256_INTERM1_EXEC =
    ARM_MK_EXEC_RULE bignum_montsqr_p256_interm1_mc;;

let bignum_montsqr_p256_interm1_core_mc_def,
    bignum_montsqr_p256_interm1_core_mc,
    BIGNUM_MONTSQR_P256_INTERM1_CORE_EXEC =
  mk_sublist_of_mc "bignum_montsqr_p256_interm1_core_mc"
    bignum_montsqr_p256_interm1_mc
    (`0`,`LENGTH bignum_montsqr_p256_interm1_mc - 4`)
    (fst BIGNUM_MONTSQR_P256_INTERM1_EXEC);;


let montsqr_p256_eqin = new_definition
  `!s1 s1' x z.
    (montsqr_p256_eqin:(armstate#armstate)->int64->int64->bool) (s1,s1') x z <=>
     (C_ARGUMENTS [z; x] s1 /\
      C_ARGUMENTS [z; x] s1' /\
      ?a. bignum_from_memory (x,4) s1 = a /\
          bignum_from_memory (x,4) s1' = a)`;;

let montsqr_p256_eqout = new_definition
  `!s1 s1' z.
    (montsqr_p256_eqout:(armstate#armstate)->int64->bool) (s1,s1') z <=>
    (?a.
      bignum_from_memory (z,4) s1 = a /\
      bignum_from_memory (z,4) s1' = a)`;;

(* This diff is generated by tools/gen-actions.py, then splitted into two
   lists to manually apply necessary equality rules on words.
   To get this diff you will need an 'original register name'
   version of the bignum_montsqr_p256_interm1_mc. *)
let actions = [
  ("equal", 0, 1, 0, 1);
  ("insert", 1, 1, 1, 2);
  ("equal", 1, 2, 2, 3);
  ("replace", 2, 24, 3, 29);
];;

let actions2 = [
  ("equal", 24, 40, 29, 45);
  ("replace", 40, 42, 45, 54);
  ("equal", 42, 124, 54, 136);
];;


let actions = break_equal_loads actions
    (snd BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC) 0x0
    (snd BIGNUM_MONTSQR_P256_INTERM1_CORE_EXEC) 0x0;;

let actions2 = break_equal_loads actions2
    (snd BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC) 0x0
    (snd BIGNUM_MONTSQR_P256_INTERM1_CORE_EXEC) 0x0;;

let equiv_goal1 = mk_equiv_statement_simple
    `ALL (nonoverlapping (z:int64,8 * 4))
      [(word pc:int64,LENGTH bignum_montsqr_p256_unopt_core_mc);
       (word pc2:int64,LENGTH bignum_montsqr_p256_interm1_core_mc)]`
    montsqr_p256_eqin
    montsqr_p256_eqout
    bignum_montsqr_p256_unopt_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`
    bignum_montsqr_p256_interm1_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;


let lemma1 = prove(`!(x:int64).
  (word_mul
        (word_zx (word_subword x (0,32):int32):int64)
        (word_zx (word_subword x (0,32):int32):int64)) =
  word (0 +
       val ((word_zx:(64)word->(32)word) x) *
       val ((word_zx:(64)word->(32)word) x))`,
  CONV_TAC WORD_BLAST);;

let lemma2 = prove(`!(x:int64).
  (word_mul
        (word_zx (word_subword x (32,32):int32):int64)
        (word_zx (word_subword x (0,32):int32)):int64) =
  word (0 +
        val ((word_zx:(64)word->(32)word) x) *
        val ((word_zx:(64)word->(32)word) (word_ushr x 32)))`,
  CONV_TAC WORD_BLAST);;

let lemma3 = prove (`!(x:int64). word_add x x = word_shl x 1`,
  CONV_TAC WORD_BLAST);;

let lemma4 = prove (`!(x:int64).
 (word_mul
   ((word_zx:(32)word->(64)word) (word_subword x (32,32)))
  ((word_zx:(32)word->(64)word) (word_subword x (32,32)))) =
 (word (0 +
   val ((word_zx:(64)word->(32)word) (word_ushr x 32)) *
   val ((word_zx:(64)word->(32)word) (word_ushr x 32))))`,
  CONV_TAC WORD_BLAST);;

let pth = prove(
  `(val (x:int64) * val (y:int64)) MOD 2 EXP 128 = val (x:int64) * val (y:int64)`,
  IMP_REWRITE_TAC[MOD_LT] THEN
  REWRITE_TAC[ARITH_RULE`2 EXP 128 = 2 EXP 64 * 2 EXP 64`] THEN
  MAP_EVERY (fun t -> ASSUME_TAC (SPEC t VAL_BOUND_64)) [`x:int64`;`y:int64`] THEN
  IMP_REWRITE_TAC[LT_MULT2]);;

let lemma5 = prove (
 `!(a'_0:int64) (a'_1:int64).
    (word_add
      (word_shl
        ((word:num->(64)word) ((val a'_0 * val a'_1) DIV 2 EXP 64))
        1)
      ((word:num->(64)word)
        (bitval
          (2 EXP 64 <=
          val
            ((word:num->(64)word) (0 + val a'_0 * val a'_1)) +
          val
            ((word:num->(64)word) (0 + val a'_0 * val a'_1)))))) =

    ((word_subword:(128)word->num#num->(64)word)
      ((word_join:(64)word->(64)word->(128)word)
        (word ((val a'_0 * val a'_1) DIV 2 EXP 64))
        (word (0 + val a'_0 * val a'_1)))
      (63,64))`,

  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?(a:int128). val a = val (a'_0:int64) * val (a'_1:int64)` MP_TAC THENL [
    EXISTS_TAC `word(val (a'_0:int64) * val (a'_1:int64)):int128` THEN
    REWRITE_TAC[VAL_WORD;DIMINDEX_128;pth];
    ALL_TAC
  ] THEN
  STRIP_TAC THEN FIRST_X_ASSUM (fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[bitval; WORD_BLAST
    `val(a:int128) DIV 2 EXP 64 = val(word_ushr a 64)`] THEN
  SPEC_TAC (`a:int128`,`a:int128`) THEN
  BITBLAST_TAC);;

let lemma6 = prove(
  `!(a'_0:int64) (a'_1:int64).
    ((word:num->(64)word)
      (bitval
        (2 EXP 64 <=
          val ((word:num->(64)word) ((val a'_0 * val a'_1) DIV 2 EXP 64)) +
          val ((word:num->(64)word) ((val a'_0 * val a'_1) DIV 2 EXP 64)) +
          bitval
            (2 EXP 64 <=
              val ((word:num->(64)word) (0 + val a'_0 * val a'_1)) +
              val ((word:num->(64)word) (0 + val a'_0 * val a'_1)))))) =

    (word_ushr
      ((word:num->(64)word) ((val a'_0 * val a'_1) DIV 2 EXP 64))
      63)`,

  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?(a:int128). val a = val (a'_0:int64) * val (a'_1:int64)` MP_TAC THENL [
    EXISTS_TAC `word(val (a'_0:int64) * val (a'_1:int64)):int128` THEN
    REWRITE_TAC[VAL_WORD;DIMINDEX_128;pth];
    ALL_TAC
  ] THEN
  STRIP_TAC THEN FIRST_X_ASSUM (fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[bitval; WORD_BLAST
    `val(a:int128) DIV 2 EXP 64 = val(word_ushr a 64)`] THEN
  SPEC_TAC (`a:int128`,`a:int128`) THEN
  BITBLAST_TAC);;



let _org_extra_word_CONV = !extra_word_CONV;;
extra_word_CONV :=
  [GEN_REWRITE_CONV I [WORD_BITMANIP_SIMP_LEMMAS; WORD_SQR64_LO; WORD_SQR64_HI;
                       WORD_MUL64_LO]]
  @ (!extra_word_CONV);;

let BIGNUM_MONTSQR_P256_CORE_EQUIV1 = time prove(equiv_goal1,

  REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC;
    fst BIGNUM_MONTSQR_P256_INTERM1_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC montsqr_p256_eqin THEN
  RULE_ASSUM_TAC (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN

  (* Start *)
  EQUIV_STEPS_TAC actions
    BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC
    BIGNUM_MONTSQR_P256_INTERM1_CORE_EXEC THEN

  (* checker:
  (fun (asl,g) ->
    let a = List.filter (fun (_,th) ->
      let t = concl th in
      if not (is_eq t) then false else
      let lhs = fst (dest_eq t) in
      lhs = `read X15 s24` || lhs = `read X4 s29'`) asl in
    if not (snd (dest_eq (concl (snd (List.nth a 0)))) =
            snd (dest_eq (concl (snd (List.nth a 1))))) then
      failwith ".."
    else ALL_TAC (asl,g))
    *)
  RULE_ASSUM_TAC(REWRITE_RULE[
    lemma1;lemma2; (* X15 of prog1 = X4 of prog2 *)
    lemma3;lemma4; (* X16 of prog1 = X5 of prog2 *)
    lemma5; (* X17 of prog1 = X10 of prog2 *)
    lemma6; (* X1 of prog1 = X15 of prog2 *)
    ]) THEN

  EQUIV_STEPS_TAC actions2
    BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC
    BIGNUM_MONTSQR_P256_INTERM1_CORE_EXEC THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[montsqr_p256_eqout;mk_equiv_regs;mk_equiv_bool_regs;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (ptr,4) state`;
                    C_ARGUMENTS] THEN
    REPEAT (TRY HINT_EXISTS_REFL_TAC THEN ASM_REWRITE_TAC[]);

    (** SUBGOAL 2. Maychange pair **)
    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;

extra_word_CONV := _org_extra_word_CONV;;


(******************************************************************************
  The second program equivalence between the intermediate program and
  fully optimized program
******************************************************************************)

let bignum_montsqr_p256_mc =
  define_from_elf "bignum_montsqr_p256_mc"
    "arm/p256/bignum_montsqr_p256.o";;

let BIGNUM_MONTSQR_P256_EXEC =
    ARM_MK_EXEC_RULE bignum_montsqr_p256_mc;;

let bignum_montsqr_p256_core_mc_def,
    bignum_montsqr_p256_core_mc,
    BIGNUM_MONTSQR_P256_CORE_EXEC =
  mk_sublist_of_mc "bignum_montsqr_p256_core_mc"
    bignum_montsqr_p256_mc
    (`0`,`LENGTH bignum_montsqr_p256_mc - 4`)
    (fst BIGNUM_MONTSQR_P256_EXEC);;


let equiv_goal2 = mk_equiv_statement_simple
    `ALL (nonoverlapping (z:int64,8 * 4))
      [(word pc:int64,LENGTH bignum_montsqr_p256_interm1_core_mc);
       (word pc2:int64,LENGTH bignum_montsqr_p256_core_mc)]`
    montsqr_p256_eqin
    montsqr_p256_eqout
    bignum_montsqr_p256_interm1_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`
    bignum_montsqr_p256_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;

(* Line numbers from bignum_montsqr_p256_core_mc (the fully optimized
   prog.) to bignum_montsqr_p256_interm1_core_mc (the intermediate prog.)
   The script that prints this map is being privately maintained by aqjune-aws.
   This map can be also printed from the instruction map of SLOTHY's output, but
   aqjune-aws does not have the converter. *)
let inst_map = [
  5;1;4;2;3;9;8;24;47;6;10;49;56;55;12;7;11;46;50;28;23;15;58;57;14;13;59;16;60;63;17;26;18;48;51;19;20;21;30;52;22;25;32;62;27;29;31;33;34;53;61;35;38;68;36;40;37;39;41;42;54;43;116;44;65;45;66;67;69;64;115;70;71;72;73;74;108;75;76;112;77;78;79;80;81;82;83;106;84;90;85;88;109;86;124;87;117;118;127;119;89;91;92;93;97;99;94;95;96;98;100;101;102;103;104;105;107;110;111;113;114;120;121;122;123;125;126;128;129;130;131;133;134;132;136;135
];;

(* (state number, (equation, fresh var)) *)
let state_to_abbrevs: (int * thm) list ref = ref [];;

let BIGNUM_MONTSQR_P256_CORE_EQUIV2 = prove(
  equiv_goal2,

  REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_MONTSQR_P256_INTERM1_CORE_EXEC;
    fst BIGNUM_MONTSQR_P256_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC montsqr_p256_eqin THEN
  RULE_ASSUM_TAC (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN

  (* Left *)
  ARM_N_STEPS_AND_ABBREV_TAC BIGNUM_MONTSQR_P256_INTERM1_CORE_EXEC
    (1--(List.length inst_map)) state_to_abbrevs None THEN

  (* Right *)
  ARM_N_STEPS_AND_REWRITE_TAC BIGNUM_MONTSQR_P256_CORE_EXEC
    (1--(List.length inst_map)) inst_map state_to_abbrevs None THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[montsqr_p256_eqout;mk_equiv_regs;mk_equiv_bool_regs;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (ptr,4) state`;
                    C_ARGUMENTS] THEN
    REPEAT (TRY HINT_EXISTS_REFL_TAC THEN ASM_REWRITE_TAC[]);

    (** SUBGOAL 2. Maychange pair **)
    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;


(******************************************************************************
  Use transitivity of two program equivalences to prove end-to-end
  correctness
******************************************************************************)

let equiv_goal = mk_equiv_statement_simple
    `ALL (nonoverlapping (z:int64,8 * 4))
      [(word pc:int64,LENGTH bignum_montsqr_p256_unopt_core_mc);
       (word pc2:int64,LENGTH bignum_montsqr_p256_core_mc)]`
    montsqr_p256_eqin
    montsqr_p256_eqout
    bignum_montsqr_p256_unopt_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`
    bignum_montsqr_p256_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;

let montsqr_p256_eqout_TRANS = prove(
  `!s s2 s'
    z. montsqr_p256_eqout (s,s') z /\ montsqr_p256_eqout (s',s2) z
    ==> montsqr_p256_eqout (s,s2) z`,
  MESON_TAC[montsqr_p256_eqout]);;

let BIGNUM_MONTSQR_P256_CORE_EQUIV = prove(equiv_goal,

  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `?pc3.
      ALL (nonoverlapping (z,8 * 4))
        [word pc:int64, LENGTH bignum_montsqr_p256_unopt_core_mc;
         word pc3:int64, LENGTH bignum_montsqr_p256_interm1_core_mc] /\
      ALL (nonoverlapping (z,8 * 4))
        [word pc3:int64, LENGTH bignum_montsqr_p256_interm1_core_mc;
         word pc2:int64, LENGTH bignum_montsqr_p256_core_mc] /\
      nonoverlapping (x,8 * 4)
        (word pc3:int64, LENGTH bignum_montsqr_p256_interm1_core_mc) /\
      4 divides val (word pc3:int64)`
      MP_TAC THENL [
    FIRST_X_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC
      [ALL;NONOVERLAPPING_CLAUSES;
       fst BIGNUM_MONTSQR_P256_INTERM1_CORE_EXEC;
       fst BIGNUM_MONTSQR_P256_CORE_EXEC;
       fst BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC;GSYM CONJ_ASSOC] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIND_HOLE_TAC;

    ALL_TAC
  ] THEN
  STRIP_TAC THEN

  EQUIV_TRANS_TAC
    (BIGNUM_MONTSQR_P256_CORE_EQUIV1,BIGNUM_MONTSQR_P256_CORE_EQUIV2)
    (montsqr_p256_eqin,montsqr_p256_eqin,montsqr_p256_eqin)
    montsqr_p256_eqout_TRANS
    (BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC,BIGNUM_MONTSQR_P256_INTERM1_CORE_EXEC,
     BIGNUM_MONTSQR_P256_CORE_EXEC));;



(******************************************************************************
          Inducing BIGNUM_MONTSQR_P256_SUBROUTINE_CORRECT
          from BIGNUM_MONTSQR_P256_UNOPT_CORE_CORRECT
******************************************************************************)

let event_n_at_pc_goal = mk_eventually_n_at_pc_statement_simple
    `nonoverlapping (word pc:int64,LENGTH
        (APPEND bignum_montsqr_p256_unopt_core_mc barrier_inst_bytes)) (z:int64,8 * 4)`
    [`z:int64`;`x:int64`] bignum_montsqr_p256_unopt_core_mc
    `\s0. C_ARGUMENTS [z;x] s0`;;

let BIGNUM_MONTSQR_P256_EVENTUALLY_N_AT_PC = prove(event_n_at_pc_goal,
  REWRITE_TAC[LENGTH_APPEND;fst BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC;BARRIER_INST_BYTES_LENGTH] THEN
  REWRITE_TAC[eventually_n_at_pc;ALL;NONOVERLAPPING_CLAUSES;C_ARGUMENTS] THEN
  SUBGOAL_THEN `4 divides (LENGTH bignum_montsqr_p256_unopt_core_mc)`
        (fun th -> REWRITE_TAC[MATCH_MP aligned_bytes_loaded_append th;
                               fst BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC]) THENL [
    REWRITE_TAC[fst BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC] THEN CONV_TAC NUM_DIVIDES_CONV;
    ALL_TAC] THEN
  REPEAT_N 3 GEN_TAC THEN
  STRIP_TAC THEN
  (* now start..! *)
  X_GEN_TAC `s0:armstate` THEN GEN_TAC THEN STRIP_TAC THEN
  (* eventually ==> eventually_n *)
  PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC);;


let BIGNUM_MONTSQR_P256_UNOPT_CORE_CORRECT_N =
  prove_ensures_n
    BIGNUM_MONTSQR_P256_UNOPT_EXEC
    BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC
    BIGNUM_MONTSQR_P256_UNOPT_CORE_CORRECT
    BIGNUM_MONTSQR_P256_EVENTUALLY_N_AT_PC;;


let BIGNUM_MONTSQR_P256_CORE_CORRECT = prove(
  `!z x a pc2.
    nonoverlapping (word pc2,LENGTH bignum_montsqr_p256_core_mc) (z,8 * 4)
    ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc2) bignum_montsqr_p256_core_mc /\
              read PC s = word pc2 /\
              C_ARGUMENTS [z; x] s /\
              bignum_from_memory (x,4) s = a)
          (\s. read PC s = word (pc2 + LENGTH bignum_montsqr_p256_core_mc) /\
              (a EXP 2 <= 2 EXP 256 * p_256
                ==> bignum_from_memory (z,4) s =
                    (inverse_mod p_256 (2 EXP 256) * a EXP 2) MOD p_256))
          (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                      X13; X14; X15; X16; X17] ,,
           MAYCHANGE MODIFIABLE_SIMD_REGS ,,
           MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  REPEAT GEN_TAC THEN
  (* Prepare pc for the original program.  *)
  SUBGOAL_THEN
    `?pc.
      nonoverlapping (word pc,LENGTH
        (APPEND bignum_montsqr_p256_unopt_core_mc barrier_inst_bytes)) (z:int64,8 * 4) /\
      nonoverlapping (word pc,LENGTH
        (APPEND bignum_montsqr_p256_unopt_core_mc barrier_inst_bytes)) (x:int64,8 * 4) /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH;
      fst BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC;NONOVERLAPPING_CLAUSES;ALL] THEN
    FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN

  PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC
    BIGNUM_MONTSQR_P256_CORE_EQUIV BIGNUM_MONTSQR_P256_UNOPT_CORE_CORRECT_N
    (BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC,BIGNUM_MONTSQR_P256_CORE_EXEC)
    (montsqr_p256_eqin,montsqr_p256_eqout));;


let BIGNUM_MONTSQR_P256_CORRECT = time prove
 (`!z x a pc.
      nonoverlapping (word pc,LENGTH bignum_montsqr_p256_mc) (z,8 * 4)
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p256_mc /\
              read PC s = word pc /\
              C_ARGUMENTS [z; x] s /\
              bignum_from_memory (x,4) s = a)
          (\s. read PC s = word (pc + LENGTH bignum_montsqr_p256_core_mc) /\
              (a EXP 2 <= 2 EXP 256 * p_256
                ==> bignum_from_memory (z,4) s =
                    (inverse_mod p_256 (2 EXP 256) * a EXP 2) MOD p_256))
          (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                      X13; X14; X15; X16; X17] ,,
           MAYCHANGE MODIFIABLE_SIMD_REGS ,,
           MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_MONTSQR_P256_CORE_CORRECT
      bignum_montsqr_p256_core_mc_def
      [fst BIGNUM_MONTSQR_P256_EXEC;
       fst BIGNUM_MONTSQR_P256_CORE_EXEC]);;

let BIGNUM_MONTSQR_P256_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p256_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p256_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = returnaddress /\
                  (a EXP 2 <= 2 EXP 256 * p_256
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256 (2 EXP 256) * a EXP 2) MOD p_256))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  REWRITE_TAC[fst BIGNUM_MONTSQR_P256_EXEC] THEN
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MONTSQR_P256_EXEC
    (REWRITE_RULE[fst BIGNUM_MONTSQR_P256_EXEC;fst BIGNUM_MONTSQR_P256_CORE_EXEC] BIGNUM_MONTSQR_P256_CORRECT));;


(******************************************************************************
          Inducing BIGNUM_AMONTSQR_P256_SUBROUTINE_CORRECT
          from BIGNUM_AMONTSQR_P256_UNOPT_CORE_CORRECT
******************************************************************************)

let BIGNUM_AMONTSQR_P256_UNOPT_CORE_CORRECT_N =
  prove_ensures_n
    BIGNUM_MONTSQR_P256_UNOPT_EXEC
    BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC
    BIGNUM_AMONTSQR_P256_UNOPT_CORE_CORRECT
    BIGNUM_MONTSQR_P256_EVENTUALLY_N_AT_PC;;

let BIGNUM_AMONTSQR_P256_CORE_CORRECT = prove(
  `!z x a pc2.
    nonoverlapping (word pc2,LENGTH bignum_montsqr_p256_core_mc) (z,8 * 4)
    ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc2) bignum_montsqr_p256_core_mc /\
              read PC s = word pc2 /\
              C_ARGUMENTS [z; x] s /\
              bignum_from_memory (x,4) s = a)
          (\s. read PC s = word (pc2 + LENGTH bignum_montsqr_p256_core_mc) /\
              (bignum_from_memory (z,4) s ==
                   inverse_mod p_256 (2 EXP 256) * a EXP 2) (mod p_256))
          (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                      X13; X14; X15; X16; X17] ,,
           MAYCHANGE MODIFIABLE_SIMD_REGS ,,
           MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  REPEAT GEN_TAC THEN
  (* Prepare pc for the original program.  *)
  SUBGOAL_THEN
    `?pc.
      nonoverlapping (word pc,LENGTH
        (APPEND bignum_montsqr_p256_unopt_core_mc barrier_inst_bytes)) (z:int64,8 * 4) /\
      nonoverlapping (word pc,LENGTH
        (APPEND bignum_montsqr_p256_unopt_core_mc barrier_inst_bytes)) (x:int64,8 * 4) /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH;
      fst BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC;NONOVERLAPPING_CLAUSES;ALL] THEN
    FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN

  PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC
    BIGNUM_MONTSQR_P256_CORE_EQUIV BIGNUM_AMONTSQR_P256_UNOPT_CORE_CORRECT_N
    (BIGNUM_MONTSQR_P256_UNOPT_CORE_EXEC,BIGNUM_MONTSQR_P256_CORE_EXEC)
    (montsqr_p256_eqin,montsqr_p256_eqout));;

let BIGNUM_AMONTSQR_P256_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p256_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p256_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + LENGTH bignum_montsqr_p256_core_mc) /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_256 (2 EXP 256) * a EXP 2) (mod p_256))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  ARM_SUB_LIST_OF_MC_TAC BIGNUM_AMONTSQR_P256_CORE_CORRECT
    bignum_montsqr_p256_core_mc_def
    [fst BIGNUM_MONTSQR_P256_EXEC;
     fst BIGNUM_MONTSQR_P256_CORE_EXEC]);;

let BIGNUM_AMONTSQR_P256_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p256_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p256_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = returnaddress /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_256 (2 EXP 256) * a EXP 2) (mod p_256))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  REWRITE_TAC[fst BIGNUM_MONTSQR_P256_EXEC] THEN
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MONTSQR_P256_EXEC
    (REWRITE_RULE[fst BIGNUM_MONTSQR_P256_EXEC;
                  fst BIGNUM_MONTSQR_P256_CORE_EXEC]
    BIGNUM_AMONTSQR_P256_CORRECT));;

