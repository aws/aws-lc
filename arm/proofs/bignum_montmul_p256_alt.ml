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
(* Montgomery multiplication modulo p_256.                                   *)
(* ========================================================================= *)

(**** print_literal_from_elf "arm/p256/bignum_montmul_p256_alt.o";;
 ****)

let bignum_montmul_p256_alt_mc =
  define_assert_from_elf "bignum_montmul_p256_alt_mc" "arm/p256/bignum_montmul_p256_alt.o"
[
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0xa9402047;       (* arm_LDP X7 X8 X2 (Immediate_Offset (iword (&0))) *)
  0x9b077c6d;       (* arm_MUL X13 X3 X7 *)
  0x9bc77c6e;       (* arm_UMULH X14 X3 X7 *)
  0x9b087c6c;       (* arm_MUL X12 X3 X8 *)
  0x9bc87c6f;       (* arm_UMULH X15 X3 X8 *)
  0xab0c01ce;       (* arm_ADDS X14 X14 X12 *)
  0xa9412849;       (* arm_LDP X9 X10 X2 (Immediate_Offset (iword (&16))) *)
  0x9b097c6c;       (* arm_MUL X12 X3 X9 *)
  0x9bc97c70;       (* arm_UMULH X16 X3 X9 *)
  0xba0c01ef;       (* arm_ADCS X15 X15 X12 *)
  0x9b0a7c6c;       (* arm_MUL X12 X3 X10 *)
  0x9bca7c63;       (* arm_UMULH X3 X3 X10 *)
  0xba0c0210;       (* arm_ADCS X16 X16 X12 *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0xa9411825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&16))) *)
  0x9b077c8c;       (* arm_MUL X12 X4 X7 *)
  0x9bc77c8b;       (* arm_UMULH X11 X4 X7 *)
  0xab0c01ce;       (* arm_ADDS X14 X14 X12 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9b087c8c;       (* arm_MUL X12 X4 X8 *)
  0x9bc87c8b;       (* arm_UMULH X11 X4 X8 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c01ef;       (* arm_ADDS X15 X15 X12 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b097c8c;       (* arm_MUL X12 X4 X9 *)
  0x9bc97c8b;       (* arm_UMULH X11 X4 X9 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0210;       (* arm_ADDS X16 X16 X12 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9b0a7c8c;       (* arm_MUL X12 X4 X10 *)
  0x9bca7c8b;       (* arm_UMULH X11 X4 X10 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0063;       (* arm_ADDS X3 X3 X12 *)
  0x9a1f0164;       (* arm_ADC X4 X11 XZR *)
  0x9b077cac;       (* arm_MUL X12 X5 X7 *)
  0x9bc77cab;       (* arm_UMULH X11 X5 X7 *)
  0xab0c01ef;       (* arm_ADDS X15 X15 X12 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b087cac;       (* arm_MUL X12 X5 X8 *)
  0x9bc87cab;       (* arm_UMULH X11 X5 X8 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0210;       (* arm_ADDS X16 X16 X12 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9b097cac;       (* arm_MUL X12 X5 X9 *)
  0x9bc97cab;       (* arm_UMULH X11 X5 X9 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0063;       (* arm_ADDS X3 X3 X12 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9b0a7cac;       (* arm_MUL X12 X5 X10 *)
  0x9bca7cab;       (* arm_UMULH X11 X5 X10 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0084;       (* arm_ADDS X4 X4 X12 *)
  0x9a1f0165;       (* arm_ADC X5 X11 XZR *)
  0x9b077ccc;       (* arm_MUL X12 X6 X7 *)
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0c0210;       (* arm_ADDS X16 X16 X12 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9b087ccc;       (* arm_MUL X12 X6 X8 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0063;       (* arm_ADDS X3 X3 X12 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9b097ccc;       (* arm_MUL X12 X6 X9 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0084;       (* arm_ADDS X4 X4 X12 *)
  0xba0b00a5;       (* arm_ADCS X5 X5 X11 *)
  0x9b0a7ccc;       (* arm_MUL X12 X6 X10 *)
  0x9bca7ccb;       (* arm_UMULH X11 X6 X10 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c00a5;       (* arm_ADDS X5 X5 X12 *)
  0x9a1f0166;       (* arm_ADC X6 X11 XZR *)
  0xd3607dac;       (* arm_LSL X12 X13 32 *)
  0xeb0c01a2;       (* arm_SUBS X2 X13 X12 *)
  0xd360fdab;       (* arm_LSR X11 X13 32 *)
  0xda0b01ad;       (* arm_SBC X13 X13 X11 *)
  0xab0c01ce;       (* arm_ADDS X14 X14 X12 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0xba020210;       (* arm_ADCS X16 X16 X2 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xd3607dcc;       (* arm_LSL X12 X14 32 *)
  0xeb0c01c2;       (* arm_SUBS X2 X14 X12 *)
  0xd360fdcb;       (* arm_LSR X11 X14 32 *)
  0xda0b01ce;       (* arm_SBC X14 X14 X11 *)
  0xab0c01ef;       (* arm_ADDS X15 X15 X12 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0xba0201ad;       (* arm_ADCS X13 X13 X2 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xd3607dec;       (* arm_LSL X12 X15 32 *)
  0xeb0c01e2;       (* arm_SUBS X2 X15 X12 *)
  0xd360fdeb;       (* arm_LSR X11 X15 32 *)
  0xda0b01ef;       (* arm_SBC X15 X15 X11 *)
  0xab0c0210;       (* arm_ADDS X16 X16 X12 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0xba0201ce;       (* arm_ADCS X14 X14 X2 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xd3607e0c;       (* arm_LSL X12 X16 32 *)
  0xeb0c0202;       (* arm_SUBS X2 X16 X12 *)
  0xd360fe0b;       (* arm_LSR X11 X16 32 *)
  0xda0b0210;       (* arm_SBC X16 X16 X11 *)
  0xab0c01ad;       (* arm_ADDS X13 X13 X12 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0xba0201ef;       (* arm_ADCS X15 X15 X2 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xab0301ad;       (* arm_ADDS X13 X13 X3 *)
  0xba0401ce;       (* arm_ADCS X14 X14 X4 *)
  0xba0501ef;       (* arm_ADCS X15 X15 X5 *)
  0xba060210;       (* arm_ADCS X16 X16 X6 *)
  0x9a9f37e2;       (* arm_CSET X2 Condition_CS *)
  0xb2407fec;       (* arm_MOV X12 (rvalue (word 4294967295)) *)
  0xb26083eb;       (* arm_MOV X11 (rvalue (word 18446744069414584321)) *)
  0xb10005a3;       (* arm_ADDS X3 X13 (rvalue (word 1)) *)
  0xfa0c01c4;       (* arm_SBCS X4 X14 X12 *)
  0xfa1f01e5;       (* arm_SBCS X5 X15 XZR *)
  0xfa0b0206;       (* arm_SBCS X6 X16 X11 *)
  0xfa1f005f;       (* arm_SBCS XZR X2 XZR *)
  0x9a8331ad;       (* arm_CSEL X13 X13 X3 Condition_CC *)
  0x9a8431ce;       (* arm_CSEL X14 X14 X4 Condition_CC *)
  0x9a8531ef;       (* arm_CSEL X15 X15 X5 Condition_CC *)
  0x9a863210;       (* arm_CSEL X16 X16 X6 Condition_CC *)
  0xa900380d;       (* arm_STP X13 X14 X0 (Immediate_Offset (iword (&0))) *)
  0xa901400f;       (* arm_STP X15 X16 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MONTMUL_P256_ALT_EXEC = ARM_MK_EXEC_RULE bignum_montmul_p256_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256 = new_definition `p_256 = 115792089210356248762697446949407573530086143415290314195533631308867097853951`;;

let BIGNUM_MONTMUL_P256_ALT_CORRECT = time prove
 (`!z x y a b pc.
        nonoverlapping (word pc,0x1f0) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p256_alt_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read PC s = word (pc + 0x1ec) /\
                  (a * b <= 2 EXP 256 * p_256
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256 (2 EXP 256) * a * b) MOD p_256))
             (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a * b <= 2 EXP 256 * p_256  assumption ***)

  ASM_CASES_TAC `a * b <= 2 EXP 256 * p_256` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC BIGNUM_MONTMUL_P256_ALT_EXEC (1--123)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN
  BIGNUM_DIGITIZE_TAC "y_" `bignum_from_memory (y,4) s0` THEN

  (*** Simulate the core pre-reduced result accumulation ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_ALT_EXEC (1--110) (1--110) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
          [sum_s106; sum_s107; sum_s108; sum_s109;
           word(bitval carry_s109)]` THEN
  SUBGOAL_THEN
   `t < 2 * p_256 /\ (2 EXP 256 * t == a * b) (mod p_256)`
  STRIP_ASSUME_TAC THENL
   [ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 256 * p
         ==> 2 EXP 256 * t < ab + 2 EXP 256 * p ==> t < 2 * p`)) THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_256; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction stage ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_ALT_EXEC (113--117) (111--123) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM WORD_BITVAL; COND_SWAP; REAL_BITVAL_NOT]) THEN
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
  SUBGOAL_THEN `carry_s117 <=> t < p_256` SUBST_ALL_TAC THENL
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

let BIGNUM_MONTMUL_P256_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc returnaddress.
        nonoverlapping (word pc,0x1f0) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p256_alt_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read PC s = returnaddress /\
                  (a * b <= 2 EXP 256 * p_256
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256 (2 EXP 256) * a * b) MOD p_256))
             (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MONTMUL_P256_ALT_EXEC
    BIGNUM_MONTMUL_P256_ALT_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Show that it also works as "almost-Montgomery" if desired. That is, even  *)
(* without the further range assumption on inputs we still get a congruence. *)
(* But the output, still 256 bits, may then not be fully reduced mod p_256.  *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_AMONTMUL_P256_ALT_CORRECT = time prove
 (`!z x y a b pc.
        nonoverlapping (word pc,0x1f0) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p256_alt_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read PC s = word (pc + 0x1ec) /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_256 (2 EXP 256) * a * b) (mod p_256))
             (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN
  BIGNUM_DIGITIZE_TAC "y_" `bignum_from_memory (y,4) s0` THEN

 (*** Simulate the core pre-reduced result accumulation ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_ALT_EXEC (1--110) (1--110) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
          [sum_s106; sum_s107; sum_s108; sum_s109;
           word(bitval carry_s109)]` THEN
  SUBGOAL_THEN
   `t < 2 EXP 256 + p_256 /\ (2 EXP 256 * t == a * b) (mod p_256)`
  STRIP_ASSUME_TAC THENL
   [ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
       `2 EXP 256 * t <= (2 EXP 256 - 1) EXP 2 + (2 EXP 256 - 1) * p
        ==> t < 2 EXP 256 + p`) THEN
      REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_256; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction stage ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256_ALT_EXEC (113--117) (111--123) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM WORD_BITVAL; COND_SWAP; REAL_BITVAL_NOT]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == ab) (mod p)
        ==> (e * i == 1) (mod p) /\ (s == t) (mod p)
            ==> (s == i * ab) (mod p)`)) THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `carry_s117 <=> t < p_256` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `320` THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[p_256; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD_BITVAL] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
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
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
  REWRITE_TAC[bitval; GSYM NOT_LT; COND_SWAP] THEN COND_CASES_TAC THEN
  EXPAND_TAC "t" THEN REWRITE_TAC[bignum_of_wordlist] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST (MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[BITVAL_CLAUSES; p_256] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REAL_INTEGER_TAC);;

let BIGNUM_AMONTMUL_P256_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc returnaddress.
        nonoverlapping (word pc,0x1f0) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p256_alt_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read PC s = returnaddress /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_256 (2 EXP 256) * a * b) (mod p_256))
             (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MONTMUL_P256_ALT_EXEC
    BIGNUM_AMONTMUL_P256_ALT_CORRECT);;
