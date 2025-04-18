(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a 4-word (256-bit) bignum to Montgomery form mod p_256k1.   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/secp256k1/bignum_tomont_p256k1.o";;
 ****)

let bignum_tomont_p256k1_mc =
  define_assert_from_elf "bignum_tomont_p256k1_mc" "arm/secp256k1/bignum_tomont_p256k1.o"
[
  0xd2807a22;       (* arm_MOV X2 (rvalue (word 977)) *)
  0xb2600042;       (* arm_ORR X2 X2 (rvalue (word 4294967296)) *)
  0xa9402027;       (* arm_LDP X7 X8 X1 (Immediate_Offset (iword (&0))) *)
  0xa9412829;       (* arm_LDP X9 X10 X1 (Immediate_Offset (iword (&16))) *)
  0x9b077c43;       (* arm_MUL X3 X2 X7 *)
  0x9b087c44;       (* arm_MUL X4 X2 X8 *)
  0x9b097c45;       (* arm_MUL X5 X2 X9 *)
  0x9b0a7c46;       (* arm_MUL X6 X2 X10 *)
  0x9bc77c47;       (* arm_UMULH X7 X2 X7 *)
  0x9bc87c48;       (* arm_UMULH X8 X2 X8 *)
  0x9bc97c49;       (* arm_UMULH X9 X2 X9 *)
  0x9bca7c4a;       (* arm_UMULH X10 X2 X10 *)
  0xab070084;       (* arm_ADDS X4 X4 X7 *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0xba0900c6;       (* arm_ADCS X6 X6 X9 *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0x9b027d47;       (* arm_MUL X7 X10 X2 *)
  0x9bc27d48;       (* arm_UMULH X8 X10 X2 *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0x9a9f3042;       (* arm_CSEL X2 X2 XZR Condition_CC *)
  0xeb020063;       (* arm_SUBS X3 X3 X2 *)
  0xfa1f0084;       (* arm_SBCS X4 X4 XZR *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xa9001003;       (* arm_STP X3 X4 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_TOMONT_P256K1_EXEC = ARM_MK_EXEC_RULE bignum_tomont_p256k1_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256k1 = new_definition `p_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`;;

let p256k1redlemma = prove
 (`!n. n <= (2 EXP 64 - 1) * (p_256k1 - 1)
       ==> let q = n DIV 2 EXP 256 + 1 in
           q < 2 EXP 64 /\
           q * p_256k1 <= n + p_256k1 /\
           n < q * p_256k1 + p_256k1`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_256k1] THEN ARITH_TAC);;

let BIGNUM_TOMONT_P256K1_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x7c) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_tomont_p256k1_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + 0x78) /\
                  bignum_from_memory (z,4) s = (2 EXP 256 * a) MOD p_256k1)
             (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  (*** Reduce to a variant of bignum_cmul_p256k1 ***)

  SUBGOAL_THEN `(2 EXP 256 * a) MOD p_256k1 = (4294968273 * a) MOD p_256k1`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_256k1] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `4294968273 * a` p256k1redlemma) THEN ANTS_TAC THENL
   [EXPAND_TAC "a" THEN REWRITE_TAC[p_256k1] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Intermediate result from initial multiply ***)

  ARM_ACCSTEPS_TAC BIGNUM_TOMONT_P256K1_EXEC (1--16) (1--16) THEN
  ABBREV_TAC
  `ca = bignum_of_wordlist [mullo_s5; sum_s13; sum_s14; sum_s15; sum_s16]` THEN
  SUBGOAL_THEN `4294968273 * a = ca` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "ca"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check((fun l -> not(l = [])) o
        intersect [`a:num`; `x:int64`; `c:int64`] o frees o concl))) THEN
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate computation ***)

  SUBGOAL_THEN `ca DIV 2 EXP 256 = val(sum_s16:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "ca" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REFL_TAC;
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE
     `n + 1 < 2 EXP 64 ==> n < 2 EXP 64 - 1`))] THEN
  ARM_STEPS_TAC BIGNUM_TOMONT_P256K1_EXEC [17] THEN
  ABBREV_TAC `q:int64 = word_add sum_s16 (word 1)` THEN
  SUBGOAL_THEN `val(sum_s16:int64) + 1 = val(q:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_1] THEN
    ASM_SIMP_TAC[DIMINDEX_64; MOD_LT];
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_TOMONT_P256K1_EXEC
   [18;20;21;22;23;25;26;27;28] (18--30) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(q:int64)`; `256`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_256k1] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `ca < val(q:int64) * p_256k1 <=> ~carry_s23` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    SUBGOAL_THEN `&(val(sum_s16:int64)):real = &(val(q:int64)) - &1`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
       `n < 2 EXP 64 - 1 ==> n + 1 < 2 EXP 64`)) THEN
      UNDISCH_THEN `word_add sum_s16 (word 1):int64 = q` (SUBST1_TAC o SYM) THEN
      SIMP_TAC[VAL_WORD_ADD; VAL_WORD_1; DIMINDEX_64; MOD_LT] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[]];
    EXPAND_TAC "ca" THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s23:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

let BIGNUM_TOMONT_P256K1_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,0x7c) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_tomont_p256k1_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory (z,4) s = (2 EXP 256 * a) MOD p_256k1)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_TOMONT_P256K1_EXEC
    BIGNUM_TOMONT_P256K1_CORRECT);;
