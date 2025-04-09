(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Negation mod p_521, field characteristic for NIST P-521 curve.            *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p521/bignum_neg_p521.o";;
 ****)

let bignum_neg_p521_mc = define_assert_from_elf "bignum_neg_p521_mc" "arm/p521/bignum_neg_p521.o"
[
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0xaa040069;       (* arm_ORR X9 X3 X4 *)
  0xa9411825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&16))) *)
  0xaa0600aa;       (* arm_ORR X10 X5 X6 *)
  0xaa0a0122;       (* arm_ORR X2 X9 X10 *)
  0xa9422027;       (* arm_LDP X7 X8 X1 (Immediate_Offset (iword (&32))) *)
  0xaa0800eb;       (* arm_ORR X11 X7 X8 *)
  0xaa0b0042;       (* arm_ORR X2 X2 X11 *)
  0xa9432829;       (* arm_LDP X9 X10 X1 (Immediate_Offset (iword (&48))) *)
  0xaa0a012b;       (* arm_ORR X11 X9 X10 *)
  0xaa0b0042;       (* arm_ORR X2 X2 X11 *)
  0xf940202b;       (* arm_LDR X11 X1 (Immediate_Offset (word 64)) *)
  0xaa0b0042;       (* arm_ORR X2 X2 X11 *)
  0xf100005f;       (* arm_CMP X2 (rvalue (word 0)) *)
  0xda9f03e2;       (* arm_CSETM X2 Condition_NE *)
  0xca020063;       (* arm_EOR X3 X3 X2 *)
  0xca020084;       (* arm_EOR X4 X4 X2 *)
  0xca0200a5;       (* arm_EOR X5 X5 X2 *)
  0xca0200c6;       (* arm_EOR X6 X6 X2 *)
  0xca0200e7;       (* arm_EOR X7 X7 X2 *)
  0xca020108;       (* arm_EOR X8 X8 X2 *)
  0xca020129;       (* arm_EOR X9 X9 X2 *)
  0xca02014a;       (* arm_EOR X10 X10 X2 *)
  0x92402042;       (* arm_AND X2 X2 (rvalue (word 511)) *)
  0xca02016b;       (* arm_EOR X11 X11 X2 *)
  0xa9001003;       (* arm_STP X3 X4 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022007;       (* arm_STP X7 X8 X0 (Immediate_Offset (iword (&32))) *)
  0xa9032809;       (* arm_STP X9 X10 X0 (Immediate_Offset (iword (&48))) *)
  0xf900200b;       (* arm_STR X11 X0 (Immediate_Offset (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_NEG_P521_EXEC = ARM_MK_EXEC_RULE bignum_neg_p521_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;

let BIGNUM_NEG_P521_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x7c) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_neg_p521_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = word (pc + 0x78) /\
                  (n <= p_521
                   ==> bignum_from_memory (z,9) s = (p_521 - n) MOD p_521))
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 9)) s0` THEN
  ARM_STEPS_TAC BIGNUM_NEG_P521_EXEC (1--30) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[WORD_UNMASK_64] THEN DISCARD_STATE_TAC "s30" THEN

  SUBGOAL_THEN `(p_521 - n) MOD p_521 = if n = 0 then 0 else p_521 - n`
  SUBST1_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o lhand o snd) THEN
    UNDISCH_TAC `n <= p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [GSYM REAL_OF_NUM_EQ] THEN
  GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
  EXPAND_TAC "n" THEN REWRITE_TAC[BIGNUM_OF_WORDLIST_EQ_0; ALL] THEN
  REWRITE_TAC[WORD_SUB_0; VAL_EQ_0; WORD_OR_EQ_0; WORD_AND_MASK] THEN
  REWRITE_TAC[CONJ_ACI; COND_SWAP; WORD_XOR_MASK] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[WORD_XOR_0; VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
  EXPAND_TAC "n" THEN
  REWRITE_TAC[p_521; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN

  SUBGOAL_THEN
   `&(val(word_xor n_8 (word 511):int64)):real =
    &(val(word 511:int64)) - &(val n_8)`
  SUBST1_TAC THENL[ALL_TAC; CONV_TAC WORD_REDUCE_CONV THEN REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `n DIV 2 EXP 512 < 2 EXP 9` MP_TAC THENL
   [UNDISCH_TAC `n <= p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (funpow 3 LAND_CONV) [SYM th]) THEN
    CONV_TAC(LAND_CONV(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
    DISCH_TAC] THEN
  ONCE_REWRITE_TAC[WORD_XOR_SYM] THEN
  REWRITE_TAC[ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
  ASM_SIMP_TAC[WORD_XOR_MASK_WORD; VAL_WORD_SUB_CASES] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `n < 2 EXP 9 ==> n <= 511`)) THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)) THEN
  SIMP_TAC[REAL_OF_NUM_SUB]);;

let BIGNUM_NEG_P521_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
        nonoverlapping (word pc,0x7c) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_neg_p521_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = returnaddress /\
                  (n <= p_521
                   ==> bignum_from_memory (z,9) s = (p_521 - n) MOD p_521))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_NEG_P521_EXEC BIGNUM_NEG_P521_CORRECT);;
