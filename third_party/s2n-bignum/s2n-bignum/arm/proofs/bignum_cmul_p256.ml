(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplication modulo p_256 of a single word and a bignum < p_256.        *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p256/bignum_cmul_p256.o";;
 ****)

let bignum_cmul_p256_mc = define_assert_from_elf "bignum_cmul_p256_mc" "arm/p256/bignum_cmul_p256.o"
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
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0x93c680ec;       (* arm_EXTR X12 X7 X6 (rvalue (word 32)) *)
  0xba0c00df;       (* arm_ADCS XZR X6 X12 *)
  0xd360fcec;       (* arm_LSR X12 X7 (rvalue (word 32)) *)
  0xba0c00ec;       (* arm_ADCS X12 X7 X12 *)
  0xd3607d8a;       (* arm_LSL X10 X12 (rvalue (word 32)) *)
  0xd360fd8b;       (* arm_LSR X11 X12 (rvalue (word 32)) *)
  0xab0a00c6;       (* arm_ADDS X6 X6 X10 *)
  0x9a0b00e7;       (* arm_ADC X7 X7 X11 *)
  0xeb0c03e9;       (* arm_NEGS X9 X12 *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xda1f016b;       (* arm_SBC X11 X11 XZR *)
  0xeb090063;       (* arm_SUBS X3 X3 X9 *)
  0xfa0a0084;       (* arm_SBCS X4 X4 X10 *)
  0xfa0b00a5;       (* arm_SBCS X5 X5 X11 *)
  0xfa0c00c6;       (* arm_SBCS X6 X6 X12 *)
  0xfa0c00e8;       (* arm_SBCS X8 X7 X12 *)
  0xab080063;       (* arm_ADDS X3 X3 X8 *)
  0xb2407fe7;       (* arm_MOV X7 (rvalue (word 4294967295)) *)
  0x8a0800e7;       (* arm_AND X7 X7 X8 *)
  0xba070084;       (* arm_ADCS X4 X4 X7 *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x8a0800e7;       (* arm_AND X7 X7 X8 *)
  0x9a0700c6;       (* arm_ADC X6 X6 X7 *)
  0xa9001003;       (* arm_STP X3 X4 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_CMUL_P256_EXEC = ARM_MK_EXEC_RULE bignum_cmul_p256_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256 = new_definition `p_256 = 115792089210356248762697446949407573530086143415290314195533631308867097853951`;;

let p256redlemma = prove
 (`!n. n <= (2 EXP 64 - 1) * (p_256 - 1)
       ==> let q = (n DIV 2 EXP 192 + n DIV 2 EXP 224 + 1) DIV 2 EXP 64 in
           q < 2 EXP 64 /\
           q * p_256 <= n + p_256 /\
           n < q * p_256 + p_256`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_256] THEN ARITH_TAC);;

let BIGNUM_CMUL_P256_CORRECT = time prove
 (`!z c x a pc.
        nonoverlapping (word pc,0xa8) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_cmul_p256_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + 0xa4) /\
                  (a < p_256
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_256))
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `c:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a < p_256 assumption for simplicity's sake ***)

  ASM_CASES_TAC `a < p_256` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC BIGNUM_CMUL_P256_EXEC (1--41)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  (*** Intermediate result from initial multiply ***)

  ARM_ACCSTEPS_TAC BIGNUM_CMUL_P256_EXEC (1--14) (1--14) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [mullo_s3; sum_s11; sum_s12; sum_s13; sum_s14] =
    val(c:int64) * a`
  ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    DISCARD_MATCHING_ASSUMPTIONS [`word(a):int64 = c`] THEN
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The quotient approximation logic ***)

  MP_TAC(SPEC `val(c:int64) * a` p256redlemma) THEN ANTS_TAC THENL
   [MATCH_MP_TAC LE_MULT2 THEN
    MP_TAC(ISPEC `c:int64` VAL_BOUND) THEN UNDISCH_TAC `a < p_256` THEN
    REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC;
    CONV_TAC(TOP_DEPTH_CONV let_CONV)] THEN
  ABBREV_TAC
   `q = ((val(c:int64) * a) DIV 2 EXP 192 +
         (val(c:int64) * a) DIV 2 EXP 224 + 1) DIV 2 EXP 64` THEN
  STRIP_TAC THEN

  ARM_ACCSTEPS_TAC BIGNUM_CMUL_P256_EXEC [17;19] (15--19) THEN
  SUBGOAL_THEN `q = val(sum_s19:int64)` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(MESON[MOD_LT]
     `q < 2 EXP 64 /\ q MOD 2 EXP 64 = a ==> q = a`) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "q" THEN
    REWRITE_TAC[DIV_MOD] THEN MATCH_MP_TAC DIV_UNIQ THEN
    EXISTS_TAC `val(sum_s17:int64)` THEN REWRITE_TAC[VAL_BOUND_64] THEN
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `bitval carry_s19` THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONJ_TAC THENL [ALL_TAC; BOUNDER_TAC[]] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    ASM_REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MOD_CONV) THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; ARITH_LE; ARITH_LT; VAL_WORD_USHR] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN SUBST1_TAC(SYM(ASSUME
     `bignum_of_wordlist [mullo_s3; sum_s11; sum_s12; sum_s13; sum_s14] =
      val(c:int64) * a`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN ARITH_TAC;
    DISCARD_MATCHING_ASSUMPTIONS [`read(rvalue y) d = c`] THEN
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Pre-reduction subtraction ****)

  ARM_ACCSTEPS_TAC BIGNUM_CMUL_P256_EXEC (21--31) (20--31) THEN
  SUBGOAL_THEN
   `2 EXP 320 * bitval carry_s23 +
    bignum_of_wordlist [sum_s27; sum_s28; sum_s29; sum_s30; sum_s31] +
    val(sum_s19:int64) * p_256 =
    2 EXP 320 * bitval carry_s31 +
    val(c:int64) * a`
  ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME
     `bignum_of_wordlist [mullo_s3; sum_s11; sum_s12; sum_s13; sum_s14] =
      val(c:int64) * a`)) THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_256] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `sum_s31:int64 = word_neg(word(bitval(val c * a < val sum_s19 * p_256))) /\
    (carry_s31 /\ ~carry_s23 <=> val(c:int64) * a < val(sum_s19:int64) * p_256)`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC FLAG_AND_MASK_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`val(sum_s19:int64) * p_256 <= val(c:int64) * a + p_256`;
        `val(c:int64) * a < val(sum_s19:int64) * p_256 + p_256`] THEN
      REWRITE_TAC[p_256; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      FIRST_ASSUM(fun th -> SUBST1_TAC(MATCH_MP
        (MESON[REAL_OF_NUM_ADD; REAL_ARITH `a:real = b + x ==> x = a - b`]
       `a = b + x ==> &x:real = &a - &b`) th) THEN MP_TAC th) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      MAP_EVERY ASM_CASES_TAC [`carry_s23:bool`; `carry_s31:bool`] THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      TRY(DISCH_THEN(K ALL_TAC) THEN BOUNDER_TAC[]) THEN
      MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
      EXPAND_TAC "a" THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256] THEN
      MATCH_MP_TAC(REAL_ARITH `y - x:real < e ==> ~(e * &1 + x = y)`) THEN
      BOUNDER_TAC[]];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction ***)

  ARM_ACCSTEPS_TAC BIGNUM_CMUL_P256_EXEC [32;35;36;39] (32--41) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(sum_s19:int64)`; `256`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `b <=> val(c:int64) * a < val(sum_s19:int64) * p_256` THEN
  REWRITE_TAC[p_256] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC
   `2 EXP 320 * bitval carry_s23 +
    bignum_of_wordlist [sum_s27; sum_s28; sum_s29; sum_s30;
                        word_neg (word (bitval b))] +
    val(sum_s19:int64) * p_256 =
    2 EXP 320 * bitval carry_s31 +
    val(c:int64) * a` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256; bignum_of_wordlist] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP
   (REAL_ARITH `a:real = b + x ==> x = a - b`)) THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  BOOL_CASES_TAC `b:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_CMUL_P256_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc returnaddress.
        nonoverlapping (word pc,0xa8) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_cmul_p256_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = returnaddress /\
                  (a < p_256
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_256))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_CMUL_P256_EXEC BIGNUM_CMUL_P256_CORRECT);;
