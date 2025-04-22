(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Montgomery multiplication modulo p_256.                                   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/equiv.ml";;
needs "arm/proofs/neon_helper.ml";;

(**** print_literal_from_elf "arm/p256/unopt/bignum_montmul_p256_base.o";;
 ****)

let bignum_montmul_p256_unopt_mc =
  define_assert_from_elf "bignum_montmul_p256_unopt_mc" "arm/p256/unopt/bignum_montmul_p256_base.o"
[
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&16))) *)
  0xa9402047;       (* arm_LDP X7 X8 X2 (Immediate_Offset (iword (&0))) *)
  0xa9412849;       (* arm_LDP X9 X10 X2 (Immediate_Offset (iword (&16))) *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9b087c8d;       (* arm_MUL X13 X4 X8 *)
  0x9bc77c6c;       (* arm_UMULH X12 X3 X7 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e0191;       (* arm_ADCS X17 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba1101ad;       (* arm_ADCS X13 X13 X17 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb04006f;       (* arm_SUBS X15 X3 X4 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23e1;       (* arm_CSETM X1 Condition_CC *)
  0xeb070111;       (* arm_SUBS X17 X8 X7 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0x9b117df0;       (* arm_MUL X16 X15 X17 *)
  0x9bd17df1;       (* arm_UMULH X17 X15 X17 *)
  0xda812021;       (* arm_CINV X1 X1 Condition_CC *)
  0xca010210;       (* arm_EOR X16 X16 X1 *)
  0xca010231;       (* arm_EOR X17 X17 X1 *)
  0xb100043f;       (* arm_CMN X1 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba1101ad;       (* arm_ADCS X13 X13 X17 *)
  0x9a0101ce;       (* arm_ADC X14 X14 X1 *)
  0xd3607d71;       (* arm_LSL X17 X11 (rvalue (word 32)) *)
  0xeb110161;       (* arm_SUBS X1 X11 X17 *)
  0xd360fd70;       (* arm_LSR X16 X11 (rvalue (word 32)) *)
  0xda10016b;       (* arm_SBC X11 X11 X16 *)
  0xab11018c;       (* arm_ADDS X12 X12 X17 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0xba0101ce;       (* arm_ADCS X14 X14 X1 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xd3607d91;       (* arm_LSL X17 X12 (rvalue (word 32)) *)
  0xeb110181;       (* arm_SUBS X1 X12 X17 *)
  0xd360fd90;       (* arm_LSR X16 X12 (rvalue (word 32)) *)
  0xda10018c;       (* arm_SBC X12 X12 X16 *)
  0xab1101ad;       (* arm_ADDS X13 X13 X17 *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0xba01016b;       (* arm_ADCS X11 X11 X1 *)
  0x9a1f018c;       (* arm_ADC X12 X12 XZR *)
  0xa900380d;       (* arm_STP X13 X14 X0 (Immediate_Offset (iword (&0))) *)
  0xa901300b;       (* arm_STP X11 X12 X0 (Immediate_Offset (iword (&16))) *)
  0x9b097cab;       (* arm_MUL X11 X5 X9 *)
  0x9b0a7ccd;       (* arm_MUL X13 X6 X10 *)
  0x9bc97cac;       (* arm_UMULH X12 X5 X9 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bca7cce;       (* arm_UMULH X14 X6 X10 *)
  0xba0e0191;       (* arm_ADCS X17 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba1101ad;       (* arm_ADCS X13 X13 X17 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb0600af;       (* arm_SUBS X15 X5 X6 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23e1;       (* arm_CSETM X1 Condition_CC *)
  0xeb090151;       (* arm_SUBS X17 X10 X9 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0x9b117df0;       (* arm_MUL X16 X15 X17 *)
  0x9bd17df1;       (* arm_UMULH X17 X15 X17 *)
  0xda812021;       (* arm_CINV X1 X1 Condition_CC *)
  0xca010210;       (* arm_EOR X16 X16 X1 *)
  0xca010231;       (* arm_EOR X17 X17 X1 *)
  0xb100043f;       (* arm_CMN X1 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba1101ad;       (* arm_ADCS X13 X13 X17 *)
  0x9a0101ce;       (* arm_ADC X14 X14 X1 *)
  0xeb0300a3;       (* arm_SUBS X3 X5 X3 *)
  0xfa0400c4;       (* arm_SBCS X4 X6 X4 *)
  0xda1f03e5;       (* arm_NGC X5 XZR *)
  0xb10004bf;       (* arm_CMN X5 (rvalue (word 1)) *)
  0xca050063;       (* arm_EOR X3 X3 X5 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xca050084;       (* arm_EOR X4 X4 X5 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xeb0900e7;       (* arm_SUBS X7 X7 X9 *)
  0xfa0a0108;       (* arm_SBCS X8 X8 X10 *)
  0xda1f03e9;       (* arm_NGC X9 XZR *)
  0xb100053f;       (* arm_CMN X9 (rvalue (word 1)) *)
  0xca0900e7;       (* arm_EOR X7 X7 X9 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xca090108;       (* arm_EOR X8 X8 X9 *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xca0900aa;       (* arm_EOR X10 X5 X9 *)
  0xa940040f;       (* arm_LDP X15 X1 X0 (Immediate_Offset (iword (&0))) *)
  0xab0f016f;       (* arm_ADDS X15 X11 X15 *)
  0xba010181;       (* arm_ADCS X1 X12 X1 *)
  0xa9412405;       (* arm_LDP X5 X9 X0 (Immediate_Offset (iword (&16))) *)
  0xba0501a5;       (* arm_ADCS X5 X13 X5 *)
  0xba0901c9;       (* arm_ADCS X9 X14 X9 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9b087c8d;       (* arm_MUL X13 X4 X8 *)
  0x9bc77c6c;       (* arm_UMULH X12 X3 X7 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e0191;       (* arm_ADCS X17 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba1101ad;       (* arm_ADCS X13 X13 X17 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb040063;       (* arm_SUBS X3 X3 X4 *)
  0xda832463;       (* arm_CNEG X3 X3 Condition_CC *)
  0xda9f23e4;       (* arm_CSETM X4 Condition_CC *)
  0xeb070111;       (* arm_SUBS X17 X8 X7 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0x9b117c70;       (* arm_MUL X16 X3 X17 *)
  0x9bd17c71;       (* arm_UMULH X17 X3 X17 *)
  0xda842084;       (* arm_CINV X4 X4 Condition_CC *)
  0xca040210;       (* arm_EOR X16 X16 X4 *)
  0xca040231;       (* arm_EOR X17 X17 X4 *)
  0xb100049f;       (* arm_CMN X4 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba1101ad;       (* arm_ADCS X13 X13 X17 *)
  0x9a0401ce;       (* arm_ADC X14 X14 X4 *)
  0xb100055f;       (* arm_CMN X10 (rvalue (word 1)) *)
  0xca0a016b;       (* arm_EOR X11 X11 X10 *)
  0xba0f016b;       (* arm_ADCS X11 X11 X15 *)
  0xca0a018c;       (* arm_EOR X12 X12 X10 *)
  0xba01018c;       (* arm_ADCS X12 X12 X1 *)
  0xca0a01ad;       (* arm_EOR X13 X13 X10 *)
  0xba0501ad;       (* arm_ADCS X13 X13 X5 *)
  0xca0a01ce;       (* arm_EOR X14 X14 X10 *)
  0xba0901ce;       (* arm_ADCS X14 X14 X9 *)
  0xba0a0043;       (* arm_ADCS X3 X2 X10 *)
  0xba1f0144;       (* arm_ADCS X4 X10 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0f01ad;       (* arm_ADDS X13 X13 X15 *)
  0xba0101ce;       (* arm_ADCS X14 X14 X1 *)
  0xba050063;       (* arm_ADCS X3 X3 X5 *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0x9a02014a;       (* arm_ADC X10 X10 X2 *)
  0xd3607d71;       (* arm_LSL X17 X11 (rvalue (word 32)) *)
  0xeb110161;       (* arm_SUBS X1 X11 X17 *)
  0xd360fd70;       (* arm_LSR X16 X11 (rvalue (word 32)) *)
  0xda10016b;       (* arm_SBC X11 X11 X16 *)
  0xab11018c;       (* arm_ADDS X12 X12 X17 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0xba0101ce;       (* arm_ADCS X14 X14 X1 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xd3607d91;       (* arm_LSL X17 X12 (rvalue (word 32)) *)
  0xeb110181;       (* arm_SUBS X1 X12 X17 *)
  0xd360fd90;       (* arm_LSR X16 X12 (rvalue (word 32)) *)
  0xda10018c;       (* arm_SBC X12 X12 X16 *)
  0xab1101ad;       (* arm_ADDS X13 X13 X17 *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0xba01016b;       (* arm_ADCS X11 X11 X1 *)
  0x9a1f018c;       (* arm_ADC X12 X12 XZR *)
  0xab0b0063;       (* arm_ADDS X3 X3 X11 *)
  0xba0c0084;       (* arm_ADCS X4 X4 X12 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0x91000542;       (* arm_ADD X2 X10 (rvalue (word 1)) *)
  0xd3607c50;       (* arm_LSL X16 X2 (rvalue (word 32)) *)
  0xab100084;       (* arm_ADDS X4 X4 X16 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xcb0203ef;       (* arm_NEG X15 X2 *)
  0xd1000610;       (* arm_SUB X16 X16 (rvalue (word 1)) *)
  0xeb0f01ad;       (* arm_SUBS X13 X13 X15 *)
  0xfa1001ce;       (* arm_SBCS X14 X14 X16 *)
  0xfa1f0063;       (* arm_SBCS X3 X3 XZR *)
  0xfa020084;       (* arm_SBCS X4 X4 X2 *)
  0xfa020147;       (* arm_SBCS X7 X10 X2 *)
  0xab0701ad;       (* arm_ADDS X13 X13 X7 *)
  0xb2407fea;       (* arm_MOV X10 (rvalue (word 4294967295)) *)
  0x8a07014a;       (* arm_AND X10 X10 X7 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xb26083ea;       (* arm_MOV X10 (rvalue (word 18446744069414584321)) *)
  0x8a07014a;       (* arm_AND X10 X10 X7 *)
  0x9a0a0084;       (* arm_ADC X4 X4 X10 *)
  0xa900380d;       (* arm_STP X13 X14 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011003;       (* arm_STP X3 X4 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MONTMUL_P256_UNOPT_EXEC = ARM_MK_EXEC_RULE bignum_montmul_p256_unopt_mc;;

(* bignum_montmul_p256_unopt_mc without ret. *)
let bignum_montmul_p256_unopt_core_mc_def,
    bignum_montmul_p256_unopt_core_mc,
    BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC =
  mk_sublist_of_mc "bignum_montmul_p256_unopt_core_mc"
    bignum_montmul_p256_unopt_mc
    (`0`,`LENGTH bignum_montmul_p256_unopt_mc - 4`)
    (fst BIGNUM_MONTMUL_P256_UNOPT_EXEC);;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

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

let p256shortredlemma = prove
 (`!n. n < 3 * p_256
       ==> let q = (n DIV 2 EXP 256) + 1 in
           q <= 3 /\
           q * p_256 <= n + p_256 /\
           n < q * p_256 + p_256`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_256] THEN ARITH_TAC);;

let BIGNUM_MONTMUL_P256_UNOPT_CORE_CORRECT = time prove
 (`!z x y a b pc.
        nonoverlapping (word pc,LENGTH bignum_montmul_p256_unopt_core_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p256_unopt_core_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read PC s = word (pc + LENGTH bignum_montmul_p256_unopt_core_mc) /\
                  (a * b <= 2 EXP 256 * p_256
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256 (2 EXP 256) * a * b) MOD p_256))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a * b <= 2 EXP 256 * p_256  assumption ***)

  ASM_CASES_TAC `a * b <= 2 EXP 256 * p_256` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC (1--175)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN
  BIGNUM_DIGITIZE_TAC "y_" `bignum_from_memory (y,4) s0` THEN

 (*** First ADK block multiplying lower halves.
  ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC
   ([5;6;8] @ (10--14) @ [20] @ (26--28)) (1--28) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [mullo_s5; sum_s26; sum_s27; sum_s28] =
    bignum_of_wordlist[x_0;x_1] * bignum_of_wordlist[y_0;y_1]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
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

  (*** the two Montgomery steps on the low half ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC (29--46) (29--46) THEN
  SUBGOAL_THEN
   `2 EXP 128 * bignum_of_wordlist [sum_s41; sum_s42; sum_s43; sum_s44] =
    bignum_of_wordlist[x_0;x_1] * bignum_of_wordlist[y_0;y_1] +
    p_256 * bignum_of_wordlist[mullo_s5; sum_s33]`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_256] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  ABBREV_TAC `L' = bignum_of_wordlist[sum_s41; sum_s42; sum_s43; sum_s44]` THEN

  (*** Second ADK block multiplying upper halves. ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC
   ([47;48;50] @ (52--56) @ [62] @ (68--70)) (47--70) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [mullo_s47; sum_s68; sum_s69; sum_s70] =
    bignum_of_wordlist[x_2;x_3] * bignum_of_wordlist[y_2;y_3]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
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

  (*** First absolute difference computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC [71;72;76;78] (71--78) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; WORD_RULE
   `word_sub (word 0) x = word_neg x`]) THEN
  SUBGOAL_THEN
   `&(bignum_of_wordlist[sum_s76;sum_s78]) =
    abs(&(bignum_of_wordlist[x_2;x_3]) - &(bignum_of_wordlist[x_0;x_1])) /\
    (carry_s72 <=> bignum_of_wordlist[x_2;x_3] < bignum_of_wordlist[x_0;x_1])`
  (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `128` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      DISCH_THEN SUBST_ALL_TAC] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_ARITH
     `abs(x - y):real = if x < y then y - x else x - y`] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0; WORD_NEG_1] THEN
    REWRITE_TAC[WORD_XOR_NOT; WORD_XOR_0] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; BITVAL_CLAUSES; DIMINDEX_64] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Second absolute difference computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC [79;80;84;86] (79--86) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; WORD_RULE
   `word_sub (word 0) x = word_neg x`]) THEN
  SUBGOAL_THEN
   `&(bignum_of_wordlist[sum_s84;sum_s86]) =
    abs(&(bignum_of_wordlist[y_0;y_1]) - &(bignum_of_wordlist[y_2;y_3])) /\
    (carry_s80 <=> bignum_of_wordlist[y_0;y_1] < bignum_of_wordlist[y_2;y_3])`
  (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `128` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      DISCH_THEN SUBST_ALL_TAC] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_ARITH
     `abs(x - y):real = if x < y then y - x else x - y`] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0; WORD_NEG_1] THEN
    REWRITE_TAC[WORD_XOR_NOT; WORD_XOR_0] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; BITVAL_CLAUSES; DIMINDEX_64] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Collective sign-magnitude representation  of middle product ***)

  ARM_STEPS_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC [87] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_XOR_MASKS]) THEN
  ABBREV_TAC
   `msgn <=> ~(bignum_of_wordlist[x_2;x_3] < bignum_of_wordlist[x_0;x_1] <=>
               bignum_of_wordlist[y_0;y_1] < bignum_of_wordlist[y_2;y_3])` THEN
  SUBGOAL_THEN
   `--(&1) pow bitval msgn *
    &(bignum_of_wordlist[sum_s76;sum_s78] *
      bignum_of_wordlist[sum_s84;sum_s86]) =
    (&(bignum_of_wordlist[x_2;x_3]) - &(bignum_of_wordlist[x_0;x_1])) *
    (&(bignum_of_wordlist[y_0;y_1]) - &(bignum_of_wordlist[y_2;y_3]))`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_SGN_ABS] THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL; GSYM REAL_OF_NUM_MUL] THEN
    MATCH_MP_TAC(REAL_RING
     `(~(z = &0) ==> x = y) ==> x * z = y * z`) THEN
    REWRITE_TAC[REAL_ENTIRE; REAL_ABS_ZERO; REAL_SUB_0; DE_MORGAN_THM] THEN
    EXPAND_TAC "msgn" THEN POP_ASSUM_LIST(K ALL_TAC) THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_POW_NEG; EVEN_BITVAL; REAL_POW_ONE] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
     `(x - y) * (u - v):real = (y - x) * (v - u)`] THEN
    REWRITE_TAC[REAL_SGN_MUL; GSYM REAL_OF_NUM_LT; real_sgn; REAL_SUB_LT] THEN
    REWRITE_TAC[MESON[]
     `(if p <=> q then x else y) =
      (if p then if q then x else y else if q then y else x)`] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** the H + L' addition (a result that we then use twice) ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC (88--94) (88--94) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s89; sum_s90; sum_s92; sum_s93; word(bitval carry_s93)] =
    bignum_of_wordlist[x_2;x_3] * bignum_of_wordlist[y_2;y_3] + L'`
  ASSUME_TAC THENL
   [EXPAND_TAC "L'" THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    REWRITE_TAC[VAL_WORD_BITVAL] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Third and final ADK block computing the mid-product ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC
   ([95;96;98] @ (100--104) @ [110] @ (116--118)) (95--118) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[mullo_s95; sum_s116; sum_s117; sum_s118] =
    bignum_of_wordlist[sum_s76;sum_s78] *
    bignum_of_wordlist[sum_s84;sum_s86]`
  (SUBST_ALL_TAC o SYM) THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
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

  (*** Big net accumulation computation absorbing cases over sign ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC
   ([121;123;125] @ (127--135)) (119--135) THEN
  SUBGOAL_THEN
   `2 EXP 128 *
    bignum_of_wordlist
      [sum_s121; sum_s123; sum_s131; sum_s132; sum_s133; sum_s134; sum_s135] =
    a * b + p_256 * (2 EXP 128 + 1) * bignum_of_wordlist[mullo_s5; sum_s33]`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    SUBGOAL_THEN
     `&a * &b +
      &p_256 * (&2 pow 128 + &1) * &(bignum_of_wordlist[mullo_s5; sum_s33]) =
      (&2 pow 128 + &1) *
      &(2 EXP 128 * bignum_of_wordlist
        [sum_s89; sum_s90; sum_s92; sum_s93; word(bitval carry_s93)]) +
      &2 pow 128 *
      -- &1 pow bitval msgn *
        &(bignum_of_wordlist[mullo_s95; sum_s116; sum_s117; sum_s118])`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[VAL_WORD_BITVAL]] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    BOOL_CASES_TAC `msgn:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BITVAL_CLAUSES; WORD_XOR_NOT; WORD_XOR_0;
                SYM(WORD_REDUCE_CONV `word_not(word 0):int64`)] THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Last two Montgomery steps to get the pre-reduced result ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC (136--154) (136--154) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
         [sum_s148; sum_s149; sum_s152; sum_s153; sum_s154]` THEN
  SUBGOAL_THEN
   `2 EXP 256 * t =
    a * b +
    p_256 * ((2 EXP 128 + 1) * bignum_of_wordlist[mullo_s5; sum_s33] +
             2 EXP 128 * bignum_of_wordlist[sum_s121; sum_s140])`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED; REAL_ADD_RID] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; ADD_ASSOC] THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC
      (RAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV o LAND_CONV)
      [SYM th]) THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256; bignum_of_wordlist] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(MAP_EVERY SUBST1_TAC o
      filter (is_ratconst o rand o concl) o CONJUNCTS) THEN
    REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  SUBGOAL_THEN
   `t < 3 * p_256 /\ (2 EXP 256 * t == a * b) (mod p_256)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NUMBER_RULE `(x + p * n:num == x) (mod p)`] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
     `ab <= 2 EXP 256 * p
      ==> 2 EXP 256 * t < ab + 2 * 2 EXP 256 * p ==> t < 3 * p`)) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    REWRITE_TAC[p_256; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
    ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Quotient approximation computation and main property ***)

  ABBREV_TAC `h = t DIV 2 EXP 256` THEN
  SUBGOAL_THEN `h < 3` ASSUME_TAC THENL
   [UNDISCH_TAC `t < 3 * p_256` THEN REWRITE_TAC[p_256] THEN
    EXPAND_TAC "h" THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sum_s154:int64 = word h` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "t"] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  MP_TAC(SPEC `t:num` p256shortredlemma) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV let_CONV) THEN STRIP_TAC THEN

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC
   ([157;158] @ (161--165)) (155--165) THEN
  SUBGOAL_THEN
   `--(&2 pow 320) * &(bitval carry_s165) +
    &(bignum_of_wordlist[sum_s161; sum_s162; sum_s163; sum_s164; sum_s165]) =
    &t - (&h + &1) * &p_256`
  ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_256] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    UNDISCH_TAC `h < 3` THEN
    SPEC_TAC(`h:num`,`h:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV ORELSEC
                        GEN_REWRITE_CONV I [BITVAL_CLAUSES])) THEN
    REPEAT CONJ_TAC THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  SUBGOAL_THEN
   `sum_s165:int64 = word_neg(word(bitval(t < (h + 1) * p_256))) /\
    (carry_s165 <=> t < (h + 1) * p_256)`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC FLAG_AND_MASK_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(h + 1) * p_256 <= t + p_256`; `t < (h + 1) * p_256 + p_256`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256] THEN ARITH_TAC;
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [SYM th] THEN
        GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV) [SYM th]) THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      BOUNDER_TAC[]];
    ALL_TAC] THEN

  (*** The final corrective masked addition ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC [166;169;170;173] (166--175) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_256` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a * b) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a * b) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV] THEN

  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`h + 1`; `256`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `topcar <=> t < (h + 1) * p_256` THEN
  REWRITE_TAC[p_256] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `--(&2 pow 320) * c + w:real = t - hp
    ==> t = (hp + w) - &2 pow 320 * c`)) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  BOOL_CASES_TAC `topcar:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_MONTMUL_P256_UNOPT_CORRECT = time prove
 (`!z x y a b pc.
        nonoverlapping (word pc,LENGTH bignum_montmul_p256_unopt_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p256_unopt_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read PC s = word (pc + LENGTH bignum_montmul_p256_unopt_core_mc) /\
                  (a * b <= 2 EXP 256 * p_256
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256 (2 EXP 256) * a * b) MOD p_256))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  ARM_SUB_LIST_OF_MC_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_CORRECT
    bignum_montmul_p256_unopt_core_mc_def
    [fst BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC;fst BIGNUM_MONTMUL_P256_UNOPT_EXEC]);;

(* ------------------------------------------------------------------------- *)
(* Show that it also works as "almost-Montgomery" if desired. That is, even  *)
(* without the further range assumption on inputs we still get a congruence. *)
(* But the output, still 256 bits, may then not be fully reduced mod p_256.  *)
(* ------------------------------------------------------------------------- *)

let p256genshortredlemma = prove
 (`!n. n < 3 * 2 EXP 256
       ==> let q = (n DIV 2 EXP 256) + 1 in
           q <= 3 /\
           q * p_256 <= n + p_256 /\
           n < q * p_256 + p_256`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_256] THEN ARITH_TAC);;

let BIGNUM_AMONTMUL_P256_UNOPT_CORE_CORRECT = time prove
 (`!z x y a b pc.
        nonoverlapping (word pc,LENGTH bignum_montmul_p256_unopt_core_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p256_unopt_core_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read PC s = word (pc + LENGTH bignum_montmul_p256_unopt_core_mc) /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_256 (2 EXP 256) * a * b) (mod p_256))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN
  BIGNUM_DIGITIZE_TAC "y_" `bignum_from_memory (y,4) s0` THEN

 (*** First ADK block multiplying lower halves.
  ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC
   ([5;6;8] @ (10--14) @ [20] @ (26--28)) (1--28) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [mullo_s5; sum_s26; sum_s27; sum_s28] =
    bignum_of_wordlist[x_0;x_1] * bignum_of_wordlist[y_0;y_1]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
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

  (*** the two Montgomery steps on the low half ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC (29--46) (29--46) THEN
  SUBGOAL_THEN
   `2 EXP 128 * bignum_of_wordlist [sum_s41; sum_s42; sum_s43; sum_s44] =
    bignum_of_wordlist[x_0;x_1] * bignum_of_wordlist[y_0;y_1] +
    p_256 * bignum_of_wordlist[mullo_s5; sum_s33]`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_256] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  ABBREV_TAC `L' = bignum_of_wordlist[sum_s41; sum_s42; sum_s43; sum_s44]` THEN

 (*** Second ADK block multiplying upper halves.
  ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC
   ([47;48;50] @ (52--56) @ [62] @ (68--70)) (47--70) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [mullo_s47; sum_s68; sum_s69; sum_s70] =
    bignum_of_wordlist[x_2;x_3] * bignum_of_wordlist[y_2;y_3]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
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

  (*** First absolute difference computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC [71;72;76;78] (71--78) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; WORD_RULE
   `word_sub (word 0) x = word_neg x`]) THEN
  SUBGOAL_THEN
   `&(bignum_of_wordlist[sum_s76;sum_s78]) =
    abs(&(bignum_of_wordlist[x_2;x_3]) - &(bignum_of_wordlist[x_0;x_1])) /\
    (carry_s72 <=> bignum_of_wordlist[x_2;x_3] < bignum_of_wordlist[x_0;x_1])`
  (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `128` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      DISCH_THEN SUBST_ALL_TAC] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_ARITH
     `abs(x - y):real = if x < y then y - x else x - y`] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0; WORD_NEG_1] THEN
    REWRITE_TAC[WORD_XOR_NOT; WORD_XOR_0] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; BITVAL_CLAUSES; DIMINDEX_64] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Second absolute difference computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC [79;80;84;86] (79--86) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; WORD_RULE
   `word_sub (word 0) x = word_neg x`]) THEN
  SUBGOAL_THEN
   `&(bignum_of_wordlist[sum_s84;sum_s86]) =
    abs(&(bignum_of_wordlist[y_0;y_1]) - &(bignum_of_wordlist[y_2;y_3])) /\
    (carry_s80 <=> bignum_of_wordlist[y_0;y_1] < bignum_of_wordlist[y_2;y_3])`
  (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `128` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      DISCH_THEN SUBST_ALL_TAC] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_ARITH
     `abs(x - y):real = if x < y then y - x else x - y`] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0; WORD_NEG_1] THEN
    REWRITE_TAC[WORD_XOR_NOT; WORD_XOR_0] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; BITVAL_CLAUSES; DIMINDEX_64] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Collective sign-magnitude representation  of middle product ***)

  ARM_STEPS_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC [87] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_XOR_MASKS]) THEN
  ABBREV_TAC
   `msgn <=> ~(bignum_of_wordlist[x_2;x_3] < bignum_of_wordlist[x_0;x_1] <=>
               bignum_of_wordlist[y_0;y_1] < bignum_of_wordlist[y_2;y_3])` THEN
  SUBGOAL_THEN
   `--(&1) pow bitval msgn *
    &(bignum_of_wordlist[sum_s76;sum_s78] *
      bignum_of_wordlist[sum_s84;sum_s86]) =
    (&(bignum_of_wordlist[x_2;x_3]) - &(bignum_of_wordlist[x_0;x_1])) *
    (&(bignum_of_wordlist[y_0;y_1]) - &(bignum_of_wordlist[y_2;y_3]))`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_SGN_ABS] THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL; GSYM REAL_OF_NUM_MUL] THEN
    MATCH_MP_TAC(REAL_RING
     `(~(z = &0) ==> x = y) ==> x * z = y * z`) THEN
    REWRITE_TAC[REAL_ENTIRE; REAL_ABS_ZERO; REAL_SUB_0; DE_MORGAN_THM] THEN
    EXPAND_TAC "msgn" THEN POP_ASSUM_LIST(K ALL_TAC) THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_POW_NEG; EVEN_BITVAL; REAL_POW_ONE] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
     `(x - y) * (u - v):real = (y - x) * (v - u)`] THEN
    REWRITE_TAC[REAL_SGN_MUL; GSYM REAL_OF_NUM_LT; real_sgn; REAL_SUB_LT] THEN
    REWRITE_TAC[MESON[]
     `(if p <=> q then x else y) =
      (if p then if q then x else y else if q then y else x)`] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** the H + L' addition (a result that we then use twice) ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC (88--94) (88--94) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s89; sum_s90; sum_s92; sum_s93; word(bitval carry_s93)] =
    bignum_of_wordlist[x_2;x_3] * bignum_of_wordlist[y_2;y_3] + L'`
  ASSUME_TAC THENL
   [EXPAND_TAC "L'" THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    REWRITE_TAC[VAL_WORD_BITVAL] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Third and final ADK block computing the mid-product ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC
   ([95;96;98] @ (100--104) @ [110] @ (116--118)) (95--118) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[mullo_s95; sum_s116; sum_s117; sum_s118] =
    bignum_of_wordlist[sum_s76;sum_s78] *
    bignum_of_wordlist[sum_s84;sum_s86]`
  (SUBST_ALL_TAC o SYM) THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
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

  (*** Big net accumulation computation absorbing cases over sign ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC
   ([121;123;125] @ (127--135)) (119--135) THEN
  SUBGOAL_THEN
   `2 EXP 128 *
    bignum_of_wordlist
      [sum_s121; sum_s123; sum_s131; sum_s132; sum_s133; sum_s134; sum_s135] =
    a * b + p_256 * (2 EXP 128 + 1) * bignum_of_wordlist[mullo_s5; sum_s33]`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    SUBGOAL_THEN
     `&a * &b +
      &p_256 * (&2 pow 128 + &1) * &(bignum_of_wordlist[mullo_s5; sum_s33]) =
      (&2 pow 128 + &1) *
      &(2 EXP 128 * bignum_of_wordlist
        [sum_s89; sum_s90; sum_s92; sum_s93; word(bitval carry_s93)]) +
      &2 pow 128 *
      -- &1 pow bitval msgn *
        &(bignum_of_wordlist[mullo_s95; sum_s116; sum_s117; sum_s118])`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[VAL_WORD_BITVAL]] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    BOOL_CASES_TAC `msgn:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BITVAL_CLAUSES; WORD_XOR_NOT; WORD_XOR_0;
                SYM(WORD_REDUCE_CONV `word_not(word 0):int64`)] THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Last two Montgomery steps to get the pre-reduced result ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC (136--154) (136--154) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
         [sum_s148; sum_s149; sum_s152; sum_s153; sum_s154]` THEN
  SUBGOAL_THEN
   `2 EXP 256 * t =
    a * b +
    p_256 * ((2 EXP 128 + 1) * bignum_of_wordlist[mullo_s5; sum_s33] +
             2 EXP 128 * bignum_of_wordlist[sum_s121; sum_s140])`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED; REAL_ADD_RID] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; ADD_ASSOC] THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC
      (RAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV o LAND_CONV)
      [SYM th]) THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256; bignum_of_wordlist] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(MAP_EVERY SUBST1_TAC o
      filter (is_ratconst o rand o concl) o CONJUNCTS) THEN
    REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  SUBGOAL_THEN
   `t < 3 * 2 EXP 256 /\ (2 EXP 256 * t == a * b) (mod p_256)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NUMBER_RULE `(x + p * n:num == x) (mod p)`] THEN
    MATCH_MP_TAC(ARITH_RULE
     `2 EXP 256 * x < 2 EXP 512 * 3 ==> x < 3 * 2 EXP 256`) THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ASM_REWRITE_TAC[p_256; VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Quotient approximation computation and main property ***)

  ABBREV_TAC `h = t DIV 2 EXP 256` THEN
  SUBGOAL_THEN `h < 3` ASSUME_TAC THENL
   [UNDISCH_TAC `t < 3 * 2 EXP 256` THEN EXPAND_TAC "h" THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sum_s154:int64 = word h` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "t"] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  MP_TAC(SPEC `t:num` p256genshortredlemma) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV let_CONV) THEN STRIP_TAC THEN

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC
   ([157;158] @ (161--165)) (155--165) THEN
  SUBGOAL_THEN
   `--(&2 pow 320) * &(bitval carry_s165) +
    &(bignum_of_wordlist[sum_s161; sum_s162; sum_s163; sum_s164; sum_s165]) =
    &t - (&h + &1) * &p_256`
  ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_256] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    UNDISCH_TAC `h < 3` THEN
    SPEC_TAC(`h:num`,`h:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV ORELSEC
                        GEN_REWRITE_CONV I [BITVAL_CLAUSES])) THEN
    REPEAT CONJ_TAC THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  SUBGOAL_THEN
   `sum_s165:int64 = word_neg(word(bitval(t < (h + 1) * p_256))) /\
    (carry_s165 <=> t < (h + 1) * p_256)`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC FLAG_AND_MASK_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(h + 1) * p_256 <= t + p_256`; `t < (h + 1) * p_256 + p_256`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256] THEN ARITH_TAC;
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [SYM th] THEN
        GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV) [SYM th]) THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      BOUNDER_TAC[]];
    ALL_TAC] THEN

  (*** The final corrective masked addition ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC [166;169;170;173] (166--175) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[CONG; MOD_MOD_REFL]
   `x = y MOD n ==> (x == y) (mod n)`) THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_256` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a * b) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a * b) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`h + 1`; `256`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `topcar <=> t < (h + 1) * p_256` THEN
  REWRITE_TAC[p_256] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `--(&2 pow 320) * c + w:real = t - hp
    ==> t = (hp + w) - &2 pow 320 * c`)) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  BOOL_CASES_TAC `topcar:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_AMONTMUL_P256_UNOPT_CORRECT = time prove
 (`!z x y a b pc.
        nonoverlapping (word pc,LENGTH bignum_montmul_p256_unopt_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p256_unopt_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read PC s = word (pc + LENGTH bignum_montmul_p256_unopt_core_mc) /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_256 (2 EXP 256) * a * b) (mod p_256))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  ARM_SUB_LIST_OF_MC_TAC BIGNUM_AMONTMUL_P256_UNOPT_CORE_CORRECT
    bignum_montmul_p256_unopt_core_mc_def
    [fst BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC;fst BIGNUM_MONTMUL_P256_UNOPT_EXEC]);;


(******************************************************************************
  The first program equivalence between the source program and
  its SIMD-vectorized but not instruction-scheduled program
******************************************************************************)

(* This is the intermediate program that is equivalent to both
   bignum_montmul_p256_base and bignum_montmul_p256. This is a vectorized
   version of bignum_montmul_p256_base but instructions are unscheduled. *)

let bignum_montmul_p256_interm1_ops:int list = [
    0xa9403427; (* ldp      x7, x13, [x1] *)
    0x3dc00030; (* ldr      q16, [x1] *)
    0xa9413c29; (* ldp      x9, x15, [x1, #16] *)
    0xa940104e; (* ldp      x14, x4, [x2] *)
    0x3dc00053; (* ldr      q19, [x2] *)
    0xa941404c; (* ldp      x12, x16, [x2, #16] *)
    0x3dc0043d; (* ldr      q29, [x1, #16] *)
    0x3dc0045e; (* ldr      q30, [x2, #16] *)
    0x4e901a71; (* uzp1     v17.4s, v19.4s, v16.4s *)
    0x4ea00a72; (* rev64    v18.4s, v19.4s *)
    0x4e901a1c; (* uzp1     v28.4s, v16.4s, v16.4s *)
    0x4eb09e58; (* mul      v24.4s, v18.4s, v16.4s *)
    0x6ea02b12; (* uaddlp   v18.2d, v24.4s *)
    0x4f605650; (* shl      v16.2d, v18.2d, #32 *)
    0x2eb18390; (* umlal    v16.2d, v28.2s, v17.2s *)
    0x4e083e02; (* mov      x2, v16.d[0] *)
    0x4e183e01; (* mov      x1, v16.d[1] *)
    0x9bce7ce5; (* umulh    x5, x7, x14 *)
    0xab010051; (* adds     x17, x2, x1 *)
    0x9bc47da3; (* umulh    x3, x13, x4 *)
    0xba0300a8; (* adcs     x8, x5, x3 *)
    0xba1f006a; (* adcs     x10, x3, xzr *)
    0xab1100a5; (* adds     x5, x5, x17 *)
    0xba080021; (* adcs     x1, x1, x8 *)
    0xba1f0148; (* adcs     x8, x10, xzr *)
    0xeb0d00f1; (* subs     x17, x7, x13 *)
    0xda912623; (* cneg     x3, x17, cc  // cc = lo, ul, last *)
    0xda9f23eb; (* csetm    x11, cc  // cc = lo, ul, last *)
    0xeb0e008a; (* subs     x10, x4, x14 *)
    0xda8a2546; (* cneg     x6, x10, cc  // cc = lo, ul, last *)
    0x9b067c71; (* mul      x17, x3, x6 *)
    0x9bc67c66; (* umulh    x6, x3, x6 *)
    0xda8b216b; (* cinv     x11, x11, cc  // cc = lo, ul, last *)
    0xca0b0231; (* eor      x17, x17, x11 *)
    0xca0b00c3; (* eor      x3, x6, x11 *)
    0xb100057f; (* cmn      x11, #0x1 *)
    0xba1100a5; (* adcs     x5, x5, x17 *)
    0xba03002a; (* adcs     x10, x1, x3 *)
    0x9a0b0101; (* adc      x1, x8, x11 *)
    0xd3607c43; (* lsl      x3, x2, #32 *)
    0xeb030051; (* subs     x17, x2, x3 *)
    0xd360fc4b; (* lsr      x11, x2, #32 *)
    0xda0b0048; (* sbc      x8, x2, x11 *)
    0xab0300a2; (* adds     x2, x5, x3 *)
    0xba0b0146; (* adcs     x6, x10, x11 *)
    0xba110023; (* adcs     x3, x1, x17 *)
    0x9a1f010a; (* adc      x10, x8, xzr *)
    0xd3607c45; (* lsl      x5, x2, #32 *)
    0xeb050051; (* subs     x17, x2, x5 *)
    0xd360fc4b; (* lsr      x11, x2, #32 *)
    0xda0b0048; (* sbc      x8, x2, x11 *)
    0xab0500c2; (* adds     x2, x6, x5 *)
    0xba0b0066; (* adcs     x6, x3, x11 *)
    0xba110141; (* adcs     x1, x10, x17 *)
    0x9a1f0111; (* adc      x17, x8, xzr *)
    0xa9001802; (* stp      x2, x6, [x0] *)
    0xa9014401; (* stp      x1, x17, [x0, #16] *)
    0x6f00e5fc; (* movi     v28.2d, #0xffffffff *)
    0x4e9e5bd6; (* uzp2     v22.4s, v30.4s, v30.4s *)
    0x0ea12ba4; (* xtn      v4.2s, v29.2d *)
    0x0ea12bdb; (* xtn      v27.2s, v30.2d *)
    0x4ea00bd7; (* rev64    v23.4s, v30.4s *)
    0x2ebbc091; (* umull    v17.2d, v4.2s, v27.2s *)
    0x2eb6c087; (* umull    v7.2d, v4.2s, v22.2s *)
    0x4e9d5bb0; (* uzp2     v16.4s, v29.4s, v29.4s *)
    0x4ebd9efd; (* mul      v29.4s, v23.4s, v29.4s *)
    0x6f601627; (* usra     v7.2d, v17.2d, #32 *)
    0x2eb6c21e; (* umull    v30.2d, v16.2s, v22.2s *)
    0x6ea02bb4; (* uaddlp   v20.2d, v29.4s *)
    0x4e3c1cf2; (* and      v18.16b, v7.16b, v28.16b *)
    0x2ebb8212; (* umlal    v18.2d, v16.2s, v27.2s *)
    0x4f605690; (* shl      v16.2d, v20.2d, #32 *)
    0x6f6014fe; (* usra     v30.2d, v7.2d, #32 *)
    0x2ebb8090; (* umlal    v16.2d, v4.2s, v27.2s *)
    0x6f60165e; (* usra     v30.2d, v18.2d, #32 *)
    0x4e083e0b; (* mov      x11, v16.d[0] *)
    0x4e183e05; (* mov      x5, v16.d[1] *)
    0x4e083fc2; (* mov      x2, v30.d[0] *)
    0xab050163; (* adds     x3, x11, x5 *)
    0x4e183fd1; (* mov      x17, v30.d[1] *)
    0xba110048; (* adcs     x8, x2, x17 *)
    0xba1f0221; (* adcs     x1, x17, xzr *)
    0xab030051; (* adds     x17, x2, x3 *)
    0xba0800a8; (* adcs     x8, x5, x8 *)
    0xba1f0021; (* adcs     x1, x1, xzr *)
    0xeb0f0122; (* subs     x2, x9, x15 *)
    0xda822446; (* cneg     x6, x2, cc  // cc = lo, ul, last *)
    0xda9f23e3; (* csetm    x3, cc  // cc = lo, ul, last *)
    0xeb0c0202; (* subs     x2, x16, x12 *)
    0xda822445; (* cneg     x5, x2, cc  // cc = lo, ul, last *)
    0x9b057cca; (* mul      x10, x6, x5 *)
    0x9bc57cc5; (* umulh    x5, x6, x5 *)
    0xda832063; (* cinv     x3, x3, cc  // cc = lo, ul, last *)
    0xca03014a; (* eor      x10, x10, x3 *)
    0xca0300a6; (* eor      x6, x5, x3 *)
    0xb100047f; (* cmn      x3, #0x1 *)
    0xba0a0222; (* adcs     x2, x17, x10 *)
    0xba060106; (* adcs     x6, x8, x6 *)
    0x9a030025; (* adc      x5, x1, x3 *)
    0xeb070127; (* subs     x7, x9, x7 *)
    0xfa0d01e3; (* sbcs     x3, x15, x13 *)
    0xda1f03f1; (* ngc      x17, xzr *)
    0xb100063f; (* cmn      x17, #0x1 *)
    0xca1100e8; (* eor      x8, x7, x17 *)
    0xba1f010d; (* adcs     x13, x8, xzr *)
    0xca11006f; (* eor      x15, x3, x17 *)
    0xba1f01e1; (* adcs     x1, x15, xzr *)
    0xeb0c01c9; (* subs     x9, x14, x12 *)
    0xfa10008e; (* sbcs     x14, x4, x16 *)
    0xda1f03e3; (* ngc      x3, xzr *)
    0xb100047f; (* cmn      x3, #0x1 *)
    0xca03012c; (* eor      x12, x9, x3 *)
    0xba1f0187; (* adcs     x7, x12, xzr *)
    0xca0301cc; (* eor      x12, x14, x3 *)
    0xba1f018c; (* adcs     x12, x12, xzr *)
    0xca03022a; (* eor      x10, x17, x3 *)
    0xa9403c04; (* ldp      x4, x15, [x0] *)
    0xab040171; (* adds     x17, x11, x4 *)
    0xba0f0050; (* adcs     x16, x2, x15 *)
    0xa9413c03; (* ldp      x3, x15, [x0, #16] *)
    0xba0300cb; (* adcs     x11, x6, x3 *)
    0xba0f00a9; (* adcs     x9, x5, x15 *)
    0x9a1f03ee; (* adc      x14, xzr, xzr *)
    0x9b077da6; (* mul      x6, x13, x7 *)
    0x9b0c7c28; (* mul      x8, x1, x12 *)
    0x9bc77da5; (* umulh    x5, x13, x7 *)
    0xab0800c3; (* adds     x3, x6, x8 *)
    0x9bcc7c22; (* umulh    x2, x1, x12 *)
    0xba0200a4; (* adcs     x4, x5, x2 *)
    0xba1f004f; (* adcs     x15, x2, xzr *)
    0xab0300a3; (* adds     x3, x5, x3 *)
    0xba040104; (* adcs     x4, x8, x4 *)
    0xba1f01ef; (* adcs     x15, x15, xzr *)
    0xeb0101a1; (* subs     x1, x13, x1 *)
    0xda812428; (* cneg     x8, x1, cc  // cc = lo, ul, last *)
    0xda9f23e5; (* csetm    x5, cc  // cc = lo, ul, last *)
    0xeb070181; (* subs     x1, x12, x7 *)
    0xda812422; (* cneg     x2, x1, cc  // cc = lo, ul, last *)
    0x9b027d07; (* mul      x7, x8, x2 *)
    0x9bc27d02; (* umulh    x2, x8, x2 *)
    0xda8520ad; (* cinv     x13, x5, cc  // cc = lo, ul, last *)
    0xca0d00e7; (* eor      x7, x7, x13 *)
    0xca0d0042; (* eor      x2, x2, x13 *)
    0xb10005bf; (* cmn      x13, #0x1 *)
    0xba070063; (* adcs     x3, x3, x7 *)
    0xba020084; (* adcs     x4, x4, x2 *)
    0x9a0d01e5; (* adc      x5, x15, x13 *)
    0xb100055f; (* cmn      x10, #0x1 *)
    0xca0a00c8; (* eor      x8, x6, x10 *)
    0xba11010f; (* adcs     x15, x8, x17 *)
    0xca0a0062; (* eor      x2, x3, x10 *)
    0xba100042; (* adcs     x2, x2, x16 *)
    0xca0a0086; (* eor      x6, x4, x10 *)
    0xba0b00c3; (* adcs     x3, x6, x11 *)
    0xca0a00a7; (* eor      x7, x5, x10 *)
    0xba0900e1; (* adcs     x1, x7, x9 *)
    0xba0a01cd; (* adcs     x13, x14, x10 *)
    0xba1f014c; (* adcs     x12, x10, xzr *)
    0x9a1f014a; (* adc      x10, x10, xzr *)
    0xab110065; (* adds     x5, x3, x17 *)
    0xba100028; (* adcs     x8, x1, x16 *)
    0xba0b01ad; (* adcs     x13, x13, x11 *)
    0xba090186; (* adcs     x6, x12, x9 *)
    0x9a0e0144; (* adc      x4, x10, x14 *)
    0xd3607de9; (* lsl      x9, x15, #32 *)
    0xeb0901e7; (* subs     x7, x15, x9 *)
    0xd360fde1; (* lsr      x1, x15, #32 *)
    0xda0101ee; (* sbc      x14, x15, x1 *)
    0xab09004a; (* adds     x10, x2, x9 *)
    0xba0100af; (* adcs     x15, x5, x1 *)
    0xba070105; (* adcs     x5, x8, x7 *)
    0x9a1f01c7; (* adc      x7, x14, xzr *)
    0xd3607d4c; (* lsl      x12, x10, #32 *)
    0xeb0c0151; (* subs     x17, x10, x12 *)
    0xd360fd49; (* lsr      x9, x10, #32 *)
    0xda090143; (* sbc      x3, x10, x9 *)
    0xab0c01ec; (* adds     x12, x15, x12 *)
    0xba0900a5; (* adcs     x5, x5, x9 *)
    0xba1100ee; (* adcs     x14, x7, x17 *)
    0x9a1f0062; (* adc      x2, x3, xzr *)
    0xab0e01ae; (* adds     x14, x13, x14 *)
    0xba0200c6; (* adcs     x6, x6, x2 *)
    0x9a1f0091; (* adc      x17, x4, xzr *)
    0x91000627; (* add      x7, x17, #0x1 *)
    0xd3607cf0; (* lsl      x16, x7, #32 *)
    0xab1000c3; (* adds     x3, x6, x16 *)
    0x9a1f0221; (* adc      x1, x17, xzr *)
    0xcb0703ef; (* neg      x15, x7 *)
    0xd100060d; (* sub      x13, x16, #0x1 *)
    0xeb0f0189; (* subs     x9, x12, x15 *)
    0xfa0d00a8; (* sbcs     x8, x5, x13 *)
    0xfa1f01cf; (* sbcs     x15, x14, xzr *)
    0xfa070063; (* sbcs     x3, x3, x7 *)
    0xfa070027; (* sbcs     x7, x1, x7 *)
    0xab070124; (* adds     x4, x9, x7 *)
    0xb2407fe6; (* mov      x6, #0xffffffff                 // #4294967295 *)
    0x8a0700d1; (* and      x17, x6, x7 *)
    0xba110108; (* adcs     x8, x8, x17 *)
    0xba1f01e5; (* adcs     x5, x15, xzr *)
    0xb26083ea; (* mov      x10, #0xffffffff00000001        // #-4294967295 *)
    0x8a070141; (* and      x1, x10, x7 *)
    0x9a01006c; (* adc      x12, x3, x1 *)
    0xa9002004; (* stp      x4, x8, [x0] *)
    0xa9013005; (* stp      x5, x12, [x0, #16] *)
    0xd65f03c0; (* ret *)
];;

let bignum_montmul_p256_interm1_mc =
  define_mc_from_intlist "bignum_montmul_p256_interm1_mc" bignum_montmul_p256_interm1_ops;;

let BIGNUM_MONTMUL_P256_INTERM1_EXEC =
    ARM_MK_EXEC_RULE bignum_montmul_p256_interm1_mc;;

let bignum_montmul_p256_interm1_core_mc_def,
    bignum_montmul_p256_interm1_core_mc,
    BIGNUM_MONTMUL_P256_INTERM1_CORE_EXEC =
  mk_sublist_of_mc "bignum_montmul_p256_interm1_core_mc"
    bignum_montmul_p256_interm1_mc
    (`0`,`LENGTH bignum_montmul_p256_interm1_mc - 4`)
    (fst BIGNUM_MONTMUL_P256_INTERM1_EXEC);;

let montmul_p256_eqin = new_definition
  `!s1 s1' x y z.
    (montmul_p256_eqin:(armstate#armstate)->int64->int64->int64->bool) (s1,s1') x y z <=>
     (C_ARGUMENTS [z; x; y] s1 /\
      C_ARGUMENTS [z; x; y] s1' /\
      ?a. bignum_from_memory (x,4) s1 = a /\
          bignum_from_memory (x,4) s1' = a /\
      (?b. bignum_from_memory (y,4) s1 = b /\
           bignum_from_memory (y,4) s1' = b))`;;

let montmul_p256_eqout = new_definition
  `!s1 s1' z.
    (montmul_p256_eqout:(armstate#armstate)->int64->bool) (s1,s1') z <=>
    (?a.
      bignum_from_memory (z,4) s1 = a /\
      bignum_from_memory (z,4) s1' = a)`;;

(* This diff is generated by tools/gen-actions.py.
   To get this diff you will need an 'original register name'
   version of the bignum_montmul_p256_interm1_mc.  *)
let actions = [
  ("equal", 0, 1, 0, 1);
  ("insert", 1, 1, 1, 2);
  ("equal", 1, 3, 2, 4);
  ("insert", 3, 3, 4, 5);
  ("equal", 3, 4, 5, 6);
  ("replace", 4, 6, 6, 17);
  ("equal", 6, 46, 17, 57);
  ("replace", 46, 49, 57, 78);
  ("equal", 49, 50, 78, 79);
  ("replace", 50, 51, 79, 80);
  ("equal", 51, 175, 80, 204)
];;

let actions = break_equal_loads actions
    (snd BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC) 0x0
    (snd BIGNUM_MONTMUL_P256_INTERM1_CORE_EXEC) 0x0;;

let equiv_goal1 = mk_equiv_statement_simple
    `ALL (nonoverlapping (z:int64,8 * 4))
      [(word pc:int64,LENGTH bignum_montmul_p256_unopt_core_mc);
       (word pc2:int64,LENGTH bignum_montmul_p256_interm1_core_mc)]`
    montmul_p256_eqin
    montmul_p256_eqout
    bignum_montmul_p256_unopt_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`
    bignum_montmul_p256_interm1_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;



let _org_extra_word_CONV = !extra_word_CONV;;
extra_word_CONV :=
  [GEN_REWRITE_CONV I [WORD_BITMANIP_SIMP_LEMMAS; WORD_MUL64_LO; WORD_MUL64_HI]]
  @ (!extra_word_CONV);;

let BIGNUM_MONTMUL_P256_CORE_EQUIV1 = prove(equiv_goal1,

  REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC;
    fst BIGNUM_MONTMUL_P256_INTERM1_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC montmul_p256_eqin THEN
  RULE_ASSUM_TAC (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN

  (* Start *)
  EQUIV_STEPS_TAC actions
    BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC
    BIGNUM_MONTMUL_P256_INTERM1_CORE_EXEC THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[montmul_p256_eqout;mk_equiv_regs;mk_equiv_bool_regs;
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

let bignum_montmul_p256_mc =
  define_from_elf "bignum_montmul_p256_mc"
    "arm/p256/bignum_montmul_p256.o";;

let BIGNUM_MONTMUL_P256_EXEC =
    ARM_MK_EXEC_RULE bignum_montmul_p256_mc;;

let bignum_montmul_p256_core_mc_def,
    bignum_montmul_p256_core_mc,
    BIGNUM_MONTMUL_P256_CORE_EXEC =
  mk_sublist_of_mc "bignum_montmul_p256_core_mc"
    bignum_montmul_p256_mc
    (`0`,`LENGTH bignum_montmul_p256_mc - 4`)
    (fst BIGNUM_MONTMUL_P256_EXEC);;


let equiv_goal2 = mk_equiv_statement_simple
    `ALL (nonoverlapping (z:int64,8 * 4))
      [(word pc:int64,LENGTH bignum_montmul_p256_interm1_core_mc);
       (word pc2:int64,LENGTH bignum_montmul_p256_core_mc)]`
    montmul_p256_eqin
    montmul_p256_eqout
    bignum_montmul_p256_interm1_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`
    bignum_montmul_p256_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;

(* Line numbers from bignum_montmul_p256_core_mc (the fully optimized
   prog.) to bignum_montmul_p256_interm1_core_mc (the intermediate prog.)
   The script that prints this map is being privately maintained by aqjune-aws.
   This map can be also printed from the instruction map of SLOTHY's output, but
   aqjune-aws does not have the converter. *)
let inst_map = [
  5;1;2;4;3;10;26;28;27;12;20;9;100;8;101;102;86;13;18;11;87;14;88;29;104;15;30;33;103;7;105;31;106;107;61;16;17;59;32;34;19;21;60;22;23;24;6;25;36;37;35;38;40;39;108;109;42;110;89;93;90;41;114;43;44;45;91;46;112;47;111;92;113;115;48;49;50;51;52;53;126;63;54;64;55;62;57;58;124;66;134;65;136;67;125;68;135;69;137;70;128;72;138;71;141;74;127;139;95;129;56;73;130;140;131;132;142;75;133;144;77;145;143;146;76;80;78;147;79;81;117;82;83;94;84;85;96;120;97;98;99;118;119;116;121;149;122;123;148;151;150;153;152;154;155;196;156;167;157;158;159;160;161;162;163;165;164;166;168;169;170;173;171;175;172;174;176;177;178;179;180;181;182;183;184;188;185;186;189;187;190;191;192;193;194;200;195;197;198;201;203;199;202;204
];;

(* (state number, (equation, fresh var)) *)
let state_to_abbrevs: (int * thm) list ref = ref [];;

let BIGNUM_MONTMUL_P256_CORE_EQUIV2 = prove(
  equiv_goal2,

  REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_MONTMUL_P256_INTERM1_CORE_EXEC;
    fst BIGNUM_MONTMUL_P256_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC montmul_p256_eqin THEN
  RULE_ASSUM_TAC (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN

  (* Left *)
  ARM_N_STEPS_AND_ABBREV_TAC BIGNUM_MONTMUL_P256_INTERM1_CORE_EXEC
    (1--(List.length inst_map)) state_to_abbrevs None THEN

  (* Right *)
  ARM_N_STEPS_AND_REWRITE_TAC BIGNUM_MONTMUL_P256_CORE_EXEC
    (1--(List.length inst_map)) inst_map state_to_abbrevs None THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[montmul_p256_eqout;mk_equiv_regs;mk_equiv_bool_regs;
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
      [(word pc:int64,LENGTH bignum_montmul_p256_unopt_core_mc);
       (word pc2:int64,LENGTH bignum_montmul_p256_core_mc)]`
    montmul_p256_eqin
    montmul_p256_eqout
    bignum_montmul_p256_unopt_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`
    bignum_montmul_p256_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;

let montmul_p256_eqout_TRANS = prove(
  `!s s2 s'
    z. montmul_p256_eqout (s,s') z /\ montmul_p256_eqout (s',s2) z
    ==> montmul_p256_eqout (s,s2) z`,
  MESON_TAC[montmul_p256_eqout]);;

let BIGNUM_MONTMUL_P256_CORE_EQUIV = prove(equiv_goal,

  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `?pc3.
      ALL (nonoverlapping (z,8 * 4))
        [word pc:int64, LENGTH bignum_montmul_p256_unopt_core_mc;
         word pc3:int64, LENGTH bignum_montmul_p256_interm1_core_mc] /\
      ALL (nonoverlapping (z,8 * 4))
        [word pc3:int64, LENGTH bignum_montmul_p256_interm1_core_mc;
         word pc2:int64, LENGTH bignum_montmul_p256_core_mc] /\
      ALL (nonoverlapping
        (word pc3:int64, LENGTH bignum_montmul_p256_interm1_core_mc))
        [x,8 * 4; y,8 * 4] /\
      4 divides val (word pc3:int64)`
      MP_TAC THENL [
    FIRST_X_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC
      [ALL;NONOVERLAPPING_CLAUSES;
       fst BIGNUM_MONTMUL_P256_INTERM1_CORE_EXEC;
       fst BIGNUM_MONTMUL_P256_CORE_EXEC;
       fst BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC;GSYM CONJ_ASSOC] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIND_HOLE_TAC;

    ALL_TAC
  ] THEN
  STRIP_TAC THEN

  EQUIV_TRANS_TAC
    (BIGNUM_MONTMUL_P256_CORE_EQUIV1,BIGNUM_MONTMUL_P256_CORE_EQUIV2)
    (montmul_p256_eqin,montmul_p256_eqin,montmul_p256_eqin)
    montmul_p256_eqout_TRANS
    (BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC,BIGNUM_MONTMUL_P256_INTERM1_CORE_EXEC,
     BIGNUM_MONTMUL_P256_CORE_EXEC));;



(******************************************************************************
          Inducing BIGNUM_MONTMUL_P256_SUBROUTINE_CORRECT
          from BIGNUM_MONTMUL_P256_UNOPT_CORE_CORRECT
******************************************************************************)

let event_n_at_pc_goal = mk_eventually_n_at_pc_statement_simple
    `nonoverlapping
      (word pc:int64,
        LENGTH (APPEND bignum_montmul_p256_unopt_core_mc barrier_inst_bytes))
      (z:int64,8 * 4)`
    [`z:int64`;`x:int64`;`y:int64`] bignum_montmul_p256_unopt_core_mc
    `\s0. C_ARGUMENTS [z;x;y] s0`;;

let BIGNUM_MONTMUL_P256_EVENTUALLY_N_AT_PC = prove(event_n_at_pc_goal,

  REWRITE_TAC[LENGTH_APPEND;fst BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC;
              BARRIER_INST_BYTES_LENGTH] THEN
  REWRITE_TAC[eventually_n_at_pc;ALL;NONOVERLAPPING_CLAUSES;C_ARGUMENTS] THEN
  SUBGOAL_THEN `4 divides (LENGTH bignum_montmul_p256_unopt_core_mc)`
        (fun th -> REWRITE_TAC[MATCH_MP aligned_bytes_loaded_append th;
                               fst BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC]) THENL [
    REWRITE_TAC[fst BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC] THEN CONV_TAC NUM_DIVIDES_CONV;
    ALL_TAC] THEN
  REPEAT_N 4 GEN_TAC THEN
  STRIP_TAC THEN
  (* now start..! *)
  X_GEN_TAC `s0:armstate` THEN GEN_TAC THEN STRIP_TAC THEN
  (* eventually ==> eventually_n *)
  PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC);;


let BIGNUM_MONTMUL_P256_UNOPT_CORE_CORRECT_N =
  prove_ensures_n
    BIGNUM_MONTMUL_P256_UNOPT_EXEC
    BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC
    BIGNUM_MONTMUL_P256_UNOPT_CORE_CORRECT
    BIGNUM_MONTMUL_P256_EVENTUALLY_N_AT_PC;;


let BIGNUM_MONTMUL_P256_CORE_CORRECT = prove(
  `!z x y a b pc2.
    nonoverlapping (word pc2,LENGTH bignum_montmul_p256_core_mc) (z,8 * 4)
    ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc2) bignum_montmul_p256_core_mc /\
              read PC s = word pc2 /\
              C_ARGUMENTS [z; x; y] s /\
              bignum_from_memory (x,4) s = a /\
              bignum_from_memory (y,4) s = b)
          (\s. read PC s = word (pc2 + LENGTH bignum_montmul_p256_core_mc) /\
               (a * b <= 2 EXP 256 * p_256
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256 (2 EXP 256) * a * b) MOD p_256))
          (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
           MAYCHANGE MODIFIABLE_SIMD_REGS ,,
           MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  REPEAT GEN_TAC THEN
  (* Prepare pc for the original program.  *)
  SUBGOAL_THEN
    `?pc.
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montmul_p256_unopt_core_mc barrier_inst_bytes)) (z:int64,8 * 4) /\
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montmul_p256_unopt_core_mc barrier_inst_bytes)) (x:int64,8 * 4) /\
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montmul_p256_unopt_core_mc barrier_inst_bytes)) (y:int64,8 * 4) /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[LENGTH_APPEND;fst BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC;
      BARRIER_INST_BYTES_LENGTH;NONOVERLAPPING_CLAUSES;ALL] THEN
    FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN

  PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC
    BIGNUM_MONTMUL_P256_CORE_EQUIV BIGNUM_MONTMUL_P256_UNOPT_CORE_CORRECT_N
    (BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC,BIGNUM_MONTMUL_P256_CORE_EXEC)
    (montmul_p256_eqin,montmul_p256_eqout));;


let BIGNUM_MONTMUL_P256_CORRECT = time prove
 (`!z x y a b pc.
      nonoverlapping (word pc,LENGTH bignum_montmul_p256_mc) (z,8 * 4)
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p256_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [z; x; y] s /\
               bignum_from_memory (x,4) s = a /\
               bignum_from_memory (y,4) s = b)
          (\s. read PC s = word (pc + LENGTH bignum_montmul_p256_core_mc) /\
                (a * b <= 2 EXP 256 * p_256
                    ==> bignum_from_memory (z,4) s =
                        (inverse_mod p_256 (2 EXP 256) * a * b) MOD p_256))
          (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
           MAYCHANGE MODIFIABLE_SIMD_REGS ,,
           MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_MONTMUL_P256_CORE_CORRECT
      bignum_montmul_p256_core_mc_def
      [fst BIGNUM_MONTMUL_P256_EXEC;fst BIGNUM_MONTMUL_P256_CORE_EXEC]);;

let BIGNUM_MONTMUL_P256_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc returnaddress.
        nonoverlapping (word pc,LENGTH bignum_montmul_p256_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p256_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read PC s = returnaddress /\
                  (a * b <= 2 EXP 256 * p_256
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256 (2 EXP 256) * a * b) MOD p_256))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  REWRITE_TAC[fst BIGNUM_MONTMUL_P256_EXEC] THEN
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MONTMUL_P256_EXEC
    (REWRITE_RULE[fst BIGNUM_MONTMUL_P256_EXEC;
                  fst BIGNUM_MONTMUL_P256_CORE_EXEC]
      BIGNUM_MONTMUL_P256_CORRECT));;


(******************************************************************************
          Inducing BIGNUM_AMONTMUL_P256_SUBROUTINE_CORRECT
          from BIGNUM_AMONTMUL_P256_UNOPT_CORE_CORRECT
******************************************************************************)

let BIGNUM_AMONTMUL_P256_UNOPT_CORE_CORRECT_N =
  prove_ensures_n
    BIGNUM_MONTMUL_P256_UNOPT_EXEC
    BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC
    BIGNUM_AMONTMUL_P256_UNOPT_CORE_CORRECT
    BIGNUM_MONTMUL_P256_EVENTUALLY_N_AT_PC;;

let BIGNUM_AMONTMUL_P256_CORE_CORRECT = prove(
  `!z x y a b pc2.
        nonoverlapping (word pc2,LENGTH bignum_montmul_p256_core_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc2) bignum_montmul_p256_core_mc /\
                  read PC s = word pc2 /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read PC s = word (pc2 + LENGTH bignum_montmul_p256_core_mc) /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_256 (2 EXP 256) * a * b) (mod p_256))
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
          (APPEND bignum_montmul_p256_unopt_core_mc barrier_inst_bytes)) (z:int64,8 * 4) /\
      nonoverlapping (word pc,LENGTH
          (APPEND bignum_montmul_p256_unopt_core_mc barrier_inst_bytes)) (x:int64,8 * 4) /\
      nonoverlapping (word pc,LENGTH
          (APPEND bignum_montmul_p256_unopt_core_mc barrier_inst_bytes)) (y:int64,8 * 4) /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH;
        fst BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC;NONOVERLAPPING_CLAUSES;ALL] THEN
    FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN

  PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC
    BIGNUM_MONTMUL_P256_CORE_EQUIV BIGNUM_AMONTMUL_P256_UNOPT_CORE_CORRECT_N
    (BIGNUM_MONTMUL_P256_UNOPT_CORE_EXEC,BIGNUM_MONTMUL_P256_CORE_EXEC)
    (montmul_p256_eqin,montmul_p256_eqout));;

let BIGNUM_AMONTMUL_P256_CORRECT = time prove
 (`!z x y a b pc.
        nonoverlapping (word pc,LENGTH bignum_montmul_p256_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p256_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read PC s = word (pc + LENGTH bignum_montmul_p256_core_mc) /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_256 (2 EXP 256) * a * b) (mod p_256))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                   X13; X14; X15; X16; X17] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_AMONTMUL_P256_CORE_CORRECT
      bignum_montmul_p256_core_mc_def
      [fst BIGNUM_MONTMUL_P256_EXEC;fst BIGNUM_MONTMUL_P256_CORE_EXEC]);;

let BIGNUM_AMONTMUL_P256_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc returnaddress.
        nonoverlapping (word pc,LENGTH bignum_montmul_p256_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p256_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read PC s = returnaddress /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_256 (2 EXP 256) * a * b) (mod p_256))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  REWRITE_TAC[fst BIGNUM_MONTMUL_P256_EXEC] THEN
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MONTMUL_P256_EXEC
    (REWRITE_RULE[fst BIGNUM_MONTMUL_P256_EXEC;
                  fst BIGNUM_MONTMUL_P256_CORE_EXEC]
    BIGNUM_AMONTMUL_P256_CORRECT));;

