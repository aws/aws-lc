(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplication modulo p_sm2 of a single word and a bignum < p_sm2.        *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/sm2/bignum_cmul_sm2.o";;
 ****)

let bignum_cmul_sm2_mc = define_assert_from_elf "bignum_cmul_sm2_mc" "arm/sm2/bignum_cmul_sm2.o"
[
  0xa9402849;       (* arm_LDP X9 X10 X2 (Immediate_Offset (iword (&0))) *)
  0xa941304b;       (* arm_LDP X11 X12 X2 (Immediate_Offset (iword (&16))) *)
  0x9b097c23;       (* arm_MUL X3 X1 X9 *)
  0x9b0a7c24;       (* arm_MUL X4 X1 X10 *)
  0x9b0b7c25;       (* arm_MUL X5 X1 X11 *)
  0x9b0c7c26;       (* arm_MUL X6 X1 X12 *)
  0x9bc97c29;       (* arm_UMULH X9 X1 X9 *)
  0x9bca7c2a;       (* arm_UMULH X10 X1 X10 *)
  0x9bcb7c2b;       (* arm_UMULH X11 X1 X11 *)
  0x9bcc7c27;       (* arm_UMULH X7 X1 X12 *)
  0xab090084;       (* arm_ADDS X4 X4 X9 *)
  0xba0a00a5;       (* arm_ADCS X5 X5 X10 *)
  0xba0b00c6;       (* arm_ADCS X6 X6 X11 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xab0700cb;       (* arm_ADDS X11 X6 X7 *)
  0xd280002a;       (* arm_MOV X10 (rvalue (word 1)) *)
  0x9a0a00e9;       (* arm_ADC X9 X7 X10 *)
  0x8b4b80ea;       (* arm_ADD X10 X7 (Shiftedreg X11 LSR 32) *)
  0x8b4a8128;       (* arm_ADD X8 X9 (Shiftedreg X10 LSR 32) *)
  0xd3607d0b;       (* arm_LSL X11 X8 32 *)
  0xeb080169;       (* arm_SUBS X9 X11 X8 *)
  0xd360fd0c;       (* arm_LSR X12 X8 32 *)
  0xda1f018a;       (* arm_SBC X10 X12 XZR *)
  0xcb0800e7;       (* arm_SUB X7 X7 X8 *)
  0xab080063;       (* arm_ADDS X3 X3 X8 *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0xba0a00a5;       (* arm_ADCS X5 X5 X10 *)
  0xba0b00c6;       (* arm_ADCS X6 X6 X11 *)
  0x9a0c00e7;       (* arm_ADC X7 X7 X12 *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0x92607ce9;       (* arm_AND X9 X7 (rvalue (word 18446744069414584320)) *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0x925ff8eb;       (* arm_AND X11 X7 (rvalue (word 18446744069414584319)) *)
  0x9a0b00c6;       (* arm_ADC X6 X6 X11 *)
  0xa9001003;       (* arm_STP X3 X4 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_CMUL_SM2_EXEC = ARM_MK_EXEC_RULE bignum_cmul_sm2_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_sm2 = new_definition `p_sm2 = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF`;;

let sm2redlemma = prove
 (`!n. n <= (2 EXP 64 - 1) * (p_sm2 - 1)
       ==> let q = (n DIV 2 EXP 192 + (1 + 2 EXP 32) *
                    n DIV 2 EXP 256 + 2 EXP 64) DIV (2 EXP 64) in
           q < 2 EXP 64 /\
           q * p_sm2 <= n + p_sm2 /\
           n < q * p_sm2 + p_sm2`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_sm2] THEN ARITH_TAC);;

let BIGNUM_CMUL_SM2_CORRECT = time prove
 (`!z c x a pc.
        nonoverlapping (word pc,0x98) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_cmul_sm2_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + 0x94) /\
                  (a < p_sm2
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_sm2))
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `c:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a < p_sm2 assumption for simplicity's sake ***)

  ASM_CASES_TAC `a < p_sm2` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC BIGNUM_CMUL_SM2_EXEC (1--37)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  (*** Intermediate result from initial multiply ***)

  ARM_ACCSTEPS_TAC BIGNUM_CMUL_SM2_EXEC (1--14) (1--14) THEN
  ABBREV_TAC `ca = val(c:int64) * a` THEN
  SUBGOAL_THEN `ca <= (2 EXP 64 - 1) * (p_sm2 - 1)` ASSUME_TAC THENL
   [EXPAND_TAC "ca" THEN MATCH_MP_TAC LE_MULT2 THEN
    ASM_SIMP_TAC[ARITH_RULE `a < n ==> a <= n - 1`; VAL_BOUND_64];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [mullo_s3; sum_s11; sum_s12; sum_s13; sum_s14] =
    val(c:int64) * a`
  (SUBST_ALL_TAC o SYM) THENL
   [EXPAND_TAC "a" THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    DISCARD_MATCHING_ASSUMPTIONS [`word(a):int64 = c`] THEN
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The computation of the quotient estimate q ***)

  MP_TAC(SPEC `ca:num` sm2redlemma) THEN ASM_REWRITE_TAC[] THEN
  LET_TAC THEN STRIP_TAC THEN
  ARM_ACCSTEPS_TAC BIGNUM_CMUL_SM2_EXEC [15;17;18;19] (15--19) THEN
  SUBGOAL_THEN `q = val(sum_s19:int64)` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE
     `!c. q < 2 EXP 64 /\ (2 EXP 64 * c < 2 EXP 64 * 1 ==> c = 0) /\
          2 EXP 64 * c + s = q ==> q = s`) THEN
    EXISTS_TAC `bitval carry_s19` THEN ASM_REWRITE_TAC[LT_MULT_LCANCEL] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["q"; "ca"] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; ADD_CLAUSES; MULT_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `ca DIV 2 EXP 256 <= p_sm2 DIV 2 EXP 192` MP_TAC THENL
     [UNDISCH_TAC `ca <= (2 EXP 64 - 1) * (p_sm2 - 1)` THEN
      REWRITE_TAC[p_sm2] THEN ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[p_sm2] THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN DISCH_TAC THEN
    ACCUMULATOR_ASSUM_LIST(fun ths -> ASSUM_LIST (fun thc ->
      MP_TAC(end_itlist CONJ (GEN_DECARRY_RULE thc ths)))) THEN
    REWRITE_TAC[VAL_WORD_USHR; REAL_OF_NUM_CLAUSES] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ARITH_TAC;
    DISCARD_MATCHING_ASSUMPTIONS [`read(rvalue y) d = c`] THEN
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Main subtraction of q * p_sm2 ***)

  ARM_ACCSTEPS_TAC BIGNUM_CMUL_SM2_EXEC (20--29) (20--29) THEN
  MP_TAC(ISPECL
   [`sum_s29:int64`;
    `&(bignum_of_wordlist[sum_s25; sum_s26; sum_s27; sum_s28]):real`;
    `256`; `ca:num`; `val(sum_s19:int64) * p_sm2`]
   MASK_AND_VALUE_FROM_CARRY_LT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`val(sum_s19:int64) * p_sm2 <= ca + p_sm2`;
        `ca < val(sum_s19:int64) * p_sm2 + p_sm2`] THEN
      REWRITE_TAC[p_sm2; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES]] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV)] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_sm2] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    REPEAT(MATCH_MP_TAC INTEGER_ADD THEN CONJ_TAC) THEN
    TRY REAL_INTEGER_TAC THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN STRIP_TAC] THEN

  (*** Final correction ***)

  ARM_ACCSTEPS_TAC BIGNUM_CMUL_SM2_EXEC [30;32;33;35] (30--37) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(sum_s19:int64)`; `256`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `b <=> ca < val(sum_s19:int64) * p_sm2` THEN
  REWRITE_TAC[REAL_ARITH
   `m - s - (w - b) * n:real = (m - w * n) + (b * n - s)`] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[REAL_ADD_RID]
   `x = (if p then y + z else y) ==> x = y + (if p then z else &0)`)) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_sm2] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `x:real = y + z <=> y = x - z`] THEN
  DISCH_THEN SUBST1_TAC THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REAL_INTEGER_TAC);;

let BIGNUM_CMUL_SM2_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc returnaddress.
        nonoverlapping (word pc,0x98) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_cmul_sm2_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = returnaddress /\
                  (a < p_sm2
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_sm2))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_CMUL_SM2_EXEC BIGNUM_CMUL_SM2_CORRECT);;
