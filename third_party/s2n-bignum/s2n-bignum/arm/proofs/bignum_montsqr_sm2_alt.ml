(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Montgomery squaring modulo p_sm2.                                         *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/sm2/bignum_montsqr_sm2_alt.o";;
 ****)

let bignum_montsqr_sm2_alt_mc =
  define_assert_from_elf "bignum_montsqr_sm2_alt_mc" "arm/sm2/bignum_montsqr_sm2_alt.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0x9b057c4b;       (* arm_MUL X11 X2 X5 *)
  0x9bc57c4c;       (* arm_UMULH X12 X2 X5 *)
  0x9b047c46;       (* arm_MUL X6 X2 X4 *)
  0x9bc47c47;       (* arm_UMULH X7 X2 X4 *)
  0xab06014a;       (* arm_ADDS X10 X10 X6 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9b047c66;       (* arm_MUL X6 X3 X4 *)
  0x9bc47c67;       (* arm_UMULH X7 X3 X4 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xab06016b;       (* arm_ADDS X11 X11 X6 *)
  0x9b057c8d;       (* arm_MUL X13 X4 X5 *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xba07018c;       (* arm_ADCS X12 X12 X7 *)
  0x9b057c66;       (* arm_MUL X6 X3 X5 *)
  0x9bc57c67;       (* arm_UMULH X7 X3 X5 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xab06018c;       (* arm_ADDS X12 X12 X6 *)
  0xba0701ad;       (* arm_ADCS X13 X13 X7 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab090129;       (* arm_ADDS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0x9a9f37e7;       (* arm_CSET X7 Condition_CS *)
  0x9bc27c46;       (* arm_UMULH X6 X2 X2 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
  0xab060129;       (* arm_ADDS X9 X9 X6 *)
  0x9b037c66;       (* arm_MUL X6 X3 X3 *)
  0xba06014a;       (* arm_ADCS X10 X10 X6 *)
  0x9bc37c66;       (* arm_UMULH X6 X3 X3 *)
  0xba06016b;       (* arm_ADCS X11 X11 X6 *)
  0x9b047c86;       (* arm_MUL X6 X4 X4 *)
  0xba06018c;       (* arm_ADCS X12 X12 X6 *)
  0x9bc47c86;       (* arm_UMULH X6 X4 X4 *)
  0xba0601ad;       (* arm_ADCS X13 X13 X6 *)
  0x9b057ca6;       (* arm_MUL X6 X5 X5 *)
  0xba0601ce;       (* arm_ADCS X14 X14 X6 *)
  0x9bc57ca6;       (* arm_UMULH X6 X5 X5 *)
  0x9a0600e7;       (* arm_ADC X7 X7 X6 *)
  0xd3607d04;       (* arm_LSL X4 X8 32 *)
  0xd360fd05;       (* arm_LSR X5 X8 32 *)
  0xeb080082;       (* arm_SUBS X2 X4 X8 *)
  0xda1f00a3;       (* arm_SBC X3 X5 XZR *)
  0xeb020129;       (* arm_SUBS X9 X9 X2 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xfa04016b;       (* arm_SBCS X11 X11 X4 *)
  0xda050108;       (* arm_SBC X8 X8 X5 *)
  0xd3607d24;       (* arm_LSL X4 X9 32 *)
  0xd360fd25;       (* arm_LSR X5 X9 32 *)
  0xeb090082;       (* arm_SUBS X2 X4 X9 *)
  0xda1f00a3;       (* arm_SBC X3 X5 XZR *)
  0xeb02014a;       (* arm_SUBS X10 X10 X2 *)
  0xfa03016b;       (* arm_SBCS X11 X11 X3 *)
  0xfa040108;       (* arm_SBCS X8 X8 X4 *)
  0xda050129;       (* arm_SBC X9 X9 X5 *)
  0xd3607d44;       (* arm_LSL X4 X10 32 *)
  0xd360fd45;       (* arm_LSR X5 X10 32 *)
  0xeb0a0082;       (* arm_SUBS X2 X4 X10 *)
  0xda1f00a3;       (* arm_SBC X3 X5 XZR *)
  0xeb02016b;       (* arm_SUBS X11 X11 X2 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xfa040129;       (* arm_SBCS X9 X9 X4 *)
  0xda05014a;       (* arm_SBC X10 X10 X5 *)
  0xd3607d64;       (* arm_LSL X4 X11 32 *)
  0xd360fd65;       (* arm_LSR X5 X11 32 *)
  0xeb0b0082;       (* arm_SUBS X2 X4 X11 *)
  0xda1f00a3;       (* arm_SBC X3 X5 XZR *)
  0xeb020108;       (* arm_SUBS X8 X8 X2 *)
  0xfa030129;       (* arm_SBCS X9 X9 X3 *)
  0xfa04014a;       (* arm_SBCS X10 X10 X4 *)
  0xda05016b;       (* arm_SBC X11 X11 X5 *)
  0xab0c0108;       (* arm_ADDS X8 X8 X12 *)
  0xba0d0129;       (* arm_ADCS X9 X9 X13 *)
  0xba0e014a;       (* arm_ADCS X10 X10 X14 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9a9f37e2;       (* arm_CSET X2 Condition_CS *)
  0xb2607fe3;       (* arm_MOV X3 (rvalue (word 18446744069414584320)) *)
  0x92c00025;       (* arm_MOVN X5 (word 1) 32 *)
  0xb100050c;       (* arm_ADDS X12 X8 (rvalue (word 1)) *)
  0xfa03012d;       (* arm_SBCS X13 X9 X3 *)
  0xba1f014e;       (* arm_ADCS X14 X10 XZR *)
  0xfa050167;       (* arm_SBCS X7 X11 X5 *)
  0xfa1f005f;       (* arm_SBCS XZR X2 XZR *)
  0x9a8c3108;       (* arm_CSEL X8 X8 X12 Condition_CC *)
  0x9a8d3129;       (* arm_CSEL X9 X9 X13 Condition_CC *)
  0x9a8e314a;       (* arm_CSEL X10 X10 X14 Condition_CC *)
  0x9a87316b;       (* arm_CSEL X11 X11 X7 Condition_CC *)
  0xa9002408;       (* arm_STP X8 X9 X0 (Immediate_Offset (iword (&0))) *)
  0xa9012c0a;       (* arm_STP X10 X11 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MONTSQR_SM2_ALT_EXEC = ARM_MK_EXEC_RULE bignum_montsqr_sm2_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_sm2 = new_definition `p_sm2 = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF`;;

let BIGNUM_MONTSQR_SM2_ALT_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x180) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_sm2_alt_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + 0x17c) /\
                  (a EXP 2 <= 2 EXP 256 * p_sm2
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_sm2 (2 EXP 256) * a EXP 2) MOD p_sm2))
             (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a EXP 2 <= 2 EXP 256 * p_sm2  assumption ***)

  ASM_CASES_TAC `a EXP 2 <= 2 EXP 256 * p_sm2` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC BIGNUM_MONTSQR_SM2_ALT_EXEC (1--95)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  (*** Simulate the core pre-reduced result accumulation ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_SM2_ALT_EXEC (1--82) (1--82) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
          [sum_s78; sum_s79; sum_s80; sum_s81; word(bitval carry_s81)]` THEN
  SUBGOAL_THEN
   `t < 2 * p_sm2 /\ (2 EXP 256 * t == a EXP 2) (mod p_sm2)`
  STRIP_ASSUME_TAC THENL
   [ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 256 * p
         ==> 2 EXP 256 * t < ab + 2 EXP 256 * p ==> t < 2 * p`)) THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_sm2; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_sm2] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction stage ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_SM2_ALT_EXEC (85--89) (83--95) THEN
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
  SUBGOAL_THEN `carry_s89 <=> t < p_sm2` SUBST_ALL_TAC THENL
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

let BIGNUM_MONTSQR_SM2_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,0x180) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_sm2_alt_mc /\
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
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MONTSQR_SM2_ALT_EXEC
    BIGNUM_MONTSQR_SM2_ALT_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Show that it also works as "almost-Montgomery" if desired. That is, even  *)
(* without the further range assumption on inputs we still get a congruence. *)
(* But the output, still 256 bits, may then not be fully reduced mod p_sm2.  *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_AMONTSQR_SM2_ALT_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x180) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_sm2_alt_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + 0x17c) /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_sm2 (2 EXP 256) * a EXP 2) (mod p_sm2))
             (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

 (*** Simulate the core pre-reduced result accumulation ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_SM2_ALT_EXEC (1--82) (1--82) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
          [sum_s78; sum_s79; sum_s80; sum_s81; word(bitval carry_s81)]` THEN
  SUBGOAL_THEN
   `t < 2 EXP 256 + p_sm2 /\ (2 EXP 256 * t == a EXP 2) (mod p_sm2)`
  STRIP_ASSUME_TAC THENL
   [ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
       `2 EXP 256 * t <= (2 EXP 256 - 1) EXP 2 + (2 EXP 256 - 1) * p
        ==> t < 2 EXP 256 + p`) THEN
      REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_sm2; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_sm2] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction stage ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_SM2_ALT_EXEC (85--89) (83--95) THEN
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
   [REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `carry_s89 <=> t < p_sm2` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `320` THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[p_sm2; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD_BITVAL] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
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
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
  REWRITE_TAC[bitval; GSYM NOT_LT; COND_SWAP] THEN COND_CASES_TAC THEN
  EXPAND_TAC "t" THEN REWRITE_TAC[bignum_of_wordlist] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST (MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[BITVAL_CLAUSES; p_sm2] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REAL_INTEGER_TAC);;

let BIGNUM_AMONTSQR_SM2_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,0x180) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_sm2_alt_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = returnaddress /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_sm2 (2 EXP 256) * a EXP 2) (mod p_sm2))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MONTSQR_SM2_ALT_EXEC
    BIGNUM_AMONTSQR_SM2_ALT_CORRECT);;
