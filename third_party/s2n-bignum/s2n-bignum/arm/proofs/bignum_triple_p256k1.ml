(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tripling modulo p_256k1, the field characteristic for secp256k1.          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/secp256k1/bignum_triple_p256k1.o";;
 ****)

let bignum_triple_p256k1_mc =
  define_assert_from_elf "bignum_triple_p256k1_mc" "arm/secp256k1/bignum_triple_p256k1.o"
[
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&16))) *)
  0xab030462;       (* arm_ADDS X2 X3 (Shiftedreg X3 LSL 1) *)
  0x93c3fc83;       (* arm_EXTR X3 X4 X3 63 *)
  0xba040063;       (* arm_ADCS X3 X3 X4 *)
  0x93c4fca4;       (* arm_EXTR X4 X5 X4 63 *)
  0xba050084;       (* arm_ADCS X4 X4 X5 *)
  0x93c5fcc5;       (* arm_EXTR X5 X6 X5 63 *)
  0xba0600a5;       (* arm_ADCS X5 X5 X6 *)
  0xd37ffcc6;       (* arm_LSR X6 X6 63 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xd2807a27;       (* arm_MOV X7 (rvalue (word 977)) *)
  0xb26000e7;       (* arm_ORR X7 X7 (rvalue (word 4294967296)) *)
  0x9b071cc6;       (* arm_MADD X6 X6 X7 X7 *)
  0xab060042;       (* arm_ADDS X2 X2 X6 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a9f30e7;       (* arm_CSEL X7 X7 XZR Condition_CC *)
  0xeb070042;       (* arm_SUBS X2 X2 X7 *)
  0xfa1f0063;       (* arm_SBCS X3 X3 XZR *)
  0xfa1f0084;       (* arm_SBCS X4 X4 XZR *)
  0xda1f00a5;       (* arm_SBC X5 X5 XZR *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_TRIPLE_P256K1_EXEC = ARM_MK_EXEC_RULE bignum_triple_p256k1_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256k1 = new_definition `p_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`;;

let p256k1veryshortredlemma = prove
 (`!n. n < 3 * 2 EXP 256
       ==> let q = n DIV 2 EXP 256 + 1 in
           q < 4 /\
           q < 2 EXP 64 /\
           q * p_256k1 <= n + p_256k1 /\
           n < q * p_256k1 + p_256k1`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_256k1] THEN ARITH_TAC);;

let BIGNUM_TRIPLE_P256K1_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x68) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_triple_p256k1_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + 0x64) /\
                  bignum_from_memory (z,4) s = (3 * a) MOD p_256k1)
             (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `3 * a` p256k1veryshortredlemma) THEN ANTS_TAC THENL
   [EXPAND_TAC "a" THEN REWRITE_TAC[p_256k1] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Intermediate result from tripling ***)

  ARM_ACCSTEPS_TAC BIGNUM_TRIPLE_P256K1_EXEC (1--11) (1--11) THEN
  ABBREV_TAC
  `ca = bignum_of_wordlist [sum_s3; sum_s5; sum_s7; sum_s9; sum_s11]` THEN
  SUBGOAL_THEN `3 * a = ca` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "ca"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_SUB_0] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(LAND_CONV REAL_POLY_CONV) THEN EXPAND_TAC "mullo_s10" THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; ARITH_LE; ARITH_LT] THEN
    REWRITE_TAC[VAL_WORD_SHL; VAL_WORD_0; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 = 1 + 63`; EXP_ADD; MOD_MULT2] THEN
    REWRITE_TAC[ADD_SUB; DIV_0; REAL_OF_NUM_MOD; GSYM REAL_OF_NUM_CLAUSES] THEN
    REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS
     [`read (rvalue y) s = x`; `word_subword a b = c`; `word_shl a b = c`] THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check((fun l -> not(l = [])) o
        intersect [`a:num`; `x:int64`; `c:int64`] o frees o concl))) THEN
    DISCARD_FLAGS_TAC] THEN

  (*** Notional quotient estimate and computed product ***)

  FIRST_ASSUM(MP_TAC o REWRITE_RULE[] o AP_TERM `\x. x DIV 2 EXP 256`) THEN
  CONV_TAC(LAND_CONV(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  ARM_STEPS_TAC BIGNUM_TRIPLE_P256K1_EXEC (12--14) THEN
  REABBREV_TAC `qp = read X6 s14` THEN

  (*** The rest of the computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_TRIPLE_P256K1_EXEC
   [15;16;17;18;20;21;22;23] (15--25) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(sum_s11:int64) + 1`; `256`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_256k1] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** The fact that a simple product doesn't overflow ***)

  SUBGOAL_THEN
    `&(val(qp:int64)):real = &4294968273 * (&(val(sum_s11:int64)) + &1)`
  SUBST_ALL_TAC THENL
   [UNDISCH_THEN
     `word (4294968273 + val(sum_s11:int64) * 4294968273):int64 = qp`
     (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[VAL_WORD; REAL_OF_NUM_CLAUSES; DIMINDEX_64] THEN
    REWRITE_TAC[ARITH_RULE `c * (s + 1) = c + s * c`] THEN
    MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(sum_s11:int64) + 1 < 4` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `ca < (val(sum_s11:int64) + 1) * p_256k1 <=> ~carry_s18`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    EXPAND_TAC "ca" THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s18:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

let BIGNUM_TRIPLE_P256K1_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,0x68) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_triple_p256k1_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory (z,4) s = (3 * a) MOD p_256k1)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_TRIPLE_P256K1_EXEC
    BIGNUM_TRIPLE_P256K1_CORRECT);;
