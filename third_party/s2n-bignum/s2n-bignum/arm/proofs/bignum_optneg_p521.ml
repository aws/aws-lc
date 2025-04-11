(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Optional negation mod p_521, field characteristic for NIST P-521 curve.   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p521/bignum_optneg_p521.o";;
 ****)

let bignum_optneg_p521_mc = define_assert_from_elf "bignum_optneg_p521_mc" "arm/p521/bignum_optneg_p521.o"
[
  0xa9401444;       (* arm_LDP X4 X5 X2 (Immediate_Offset (iword (&0))) *)
  0xaa05008a;       (* arm_ORR X10 X4 X5 *)
  0xa9411c46;       (* arm_LDP X6 X7 X2 (Immediate_Offset (iword (&16))) *)
  0xaa0700cb;       (* arm_ORR X11 X6 X7 *)
  0xaa0b0143;       (* arm_ORR X3 X10 X11 *)
  0xa9422448;       (* arm_LDP X8 X9 X2 (Immediate_Offset (iword (&32))) *)
  0xaa09010c;       (* arm_ORR X12 X8 X9 *)
  0xaa0c0063;       (* arm_ORR X3 X3 X12 *)
  0xa9432c4a;       (* arm_LDP X10 X11 X2 (Immediate_Offset (iword (&48))) *)
  0xaa0b014c;       (* arm_ORR X12 X10 X11 *)
  0xaa0c0063;       (* arm_ORR X3 X3 X12 *)
  0xf940204c;       (* arm_LDR X12 X2 (Immediate_Offset (word 64)) *)
  0xaa0c0063;       (* arm_ORR X3 X3 X12 *)
  0xf100007f;       (* arm_CMP X3 (rvalue (word 0)) *)
  0xda9f03e3;       (* arm_CSETM X3 Condition_NE *)
  0xf100003f;       (* arm_CMP X1 (rvalue (word 0)) *)
  0x9a8303e3;       (* arm_CSEL X3 XZR X3 Condition_EQ *)
  0xca030084;       (* arm_EOR X4 X4 X3 *)
  0xca0300a5;       (* arm_EOR X5 X5 X3 *)
  0xca0300c6;       (* arm_EOR X6 X6 X3 *)
  0xca0300e7;       (* arm_EOR X7 X7 X3 *)
  0xca030108;       (* arm_EOR X8 X8 X3 *)
  0xca030129;       (* arm_EOR X9 X9 X3 *)
  0xca03014a;       (* arm_EOR X10 X10 X3 *)
  0xca03016b;       (* arm_EOR X11 X11 X3 *)
  0x92402063;       (* arm_AND X3 X3 (rvalue (word 511)) *)
  0xca03018c;       (* arm_EOR X12 X12 X3 *)
  0xa9001404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011c06;       (* arm_STP X6 X7 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022408;       (* arm_STP X8 X9 X0 (Immediate_Offset (iword (&32))) *)
  0xa9032c0a;       (* arm_STP X10 X11 X0 (Immediate_Offset (iword (&48))) *)
  0xf900200c;       (* arm_STR X12 X0 (Immediate_Offset (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_OPTNEG_P521_EXEC = ARM_MK_EXEC_RULE bignum_optneg_p521_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;

let BIGNUM_OPTNEG_P521_CORRECT = time prove
 (`!z p x n pc.
        nonoverlapping (word pc,0x84) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_optneg_p521_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; p; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = word (pc + 0x80) /\
                  (n < p_521
                   ==> (bignum_from_memory (z,9) s =
                        if ~(p = word 0) then (p_521 - n) MOD p_521 else n)))
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `p:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 9)) s0` THEN
  ARM_STEPS_TAC BIGNUM_OPTNEG_P521_EXEC (1--32) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[WORD_UNMASK_64] THEN DISCARD_STATE_TAC "s32" THEN
  ASM_CASES_TAC `p:int64 = word 0` THEN
  ASM_REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; WORD_AND_0; WORD_XOR_0] THEN

  SUBGOAL_THEN `(p_521 - n) MOD p_521 = if n = 0 then 0 else p_521 - n`
  SUBST1_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o lhand o snd) THEN
    UNDISCH_TAC `n < p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [GSYM REAL_OF_NUM_EQ] THEN
  GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN
  ASM_SIMP_TAC[LT_IMP_LE; GSYM REAL_OF_NUM_SUB] THEN
  EXPAND_TAC "n" THEN REWRITE_TAC[BIGNUM_OF_WORDLIST_EQ_0; ALL] THEN
  REWRITE_TAC[WORD_SUB_0; VAL_EQ_0; WORD_OR_EQ_0; WORD_AND_MASK] THEN
  REWRITE_TAC[bignum_of_wordlist] THEN
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
   [UNDISCH_TAC `n < p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (funpow 3 LAND_CONV) [SYM th]) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_TAC] THEN
  ONCE_REWRITE_TAC[WORD_XOR_SYM] THEN
  REWRITE_TAC[ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
  ASM_SIMP_TAC[WORD_XOR_MASK_WORD; VAL_WORD_SUB_CASES] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `n < 2 EXP 9 ==> n <= 511`)) THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)) THEN
  SIMP_TAC[REAL_OF_NUM_SUB]);;

let BIGNUM_OPTNEG_P521_SUBROUTINE_CORRECT = time prove
 (`!z p x n pc returnaddress.
        nonoverlapping (word pc,0x84) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_optneg_p521_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; p; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = returnaddress /\
                  (n < p_521
                   ==> (bignum_from_memory (z,9) s =
                        if ~(p = word 0) then (p_521 - n) MOD p_521 else n)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_OPTNEG_P521_EXEC
    BIGNUM_OPTNEG_P521_CORRECT);;
