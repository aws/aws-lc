(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Word-level negated modular inverse.                                       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/word_negmodinv.o";;
 ****)

let word_negmodinv_mc = define_assert_from_elf "word_negmodinv_mc" "arm/generic/word_negmodinv.o"
[
  0xd37ef401;       (* arm_LSL X1 X0 (rvalue (word 2)) *)
  0xcb010001;       (* arm_SUB X1 X0 X1 *)
  0xd27f0021;       (* arm_EOR X1 X1 (rvalue (word 2)) *)
  0xd2800022;       (* arm_MOV X2 (rvalue (word 1)) *)
  0x9b010802;       (* arm_MADD X2 X0 X1 X2 *)
  0x9b027c40;       (* arm_MUL X0 X2 X2 *)
  0x9b010441;       (* arm_MADD X1 X2 X1 X1 *)
  0x9b007c02;       (* arm_MUL X2 X0 X0 *)
  0x9b010401;       (* arm_MADD X1 X0 X1 X1 *)
  0x9b027c40;       (* arm_MUL X0 X2 X2 *)
  0x9b010441;       (* arm_MADD X1 X2 X1 X1 *)
  0x9b010400;       (* arm_MADD X0 X0 X1 X1 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let WORD_NEGMODINV_EXEC = ARM_MK_EXEC_RULE word_negmodinv_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

(*** This actually works mod 32 but if anything this is more convenient ***)

let WORD_NEGMODINV_SEED_LEMMA_16 = prove
 (`!a x:int64.
        ODD a /\
        word_xor (word_sub (word a) (word_shl (word a) 2)) (word 2) = x
        ==> (a * val x + 1 == 0) (mod 16)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONG; MOD_0] THEN
  TRANS_TAC EQ_TRANS
   `(val(word a:int64) MOD 16 * val(x:int64) MOD 16 + 1) MOD 16` THEN
  REWRITE_TAC[ARITH_RULE `16 = 2 EXP 4`] THEN CONJ_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    REWRITE_TAC[VAL_MOD; NUMSEG_LT; ARITH_EQ; ARITH]] THEN
  SUBGOAL_THEN `bit 0 (word a:int64)` MP_TAC THENL
   [ASM_REWRITE_TAC[BIT_LSB_WORD];
    EXPAND_TAC "x" THEN POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
  MAP_EVERY ASM_CASES_TAC
   [`bit 1 (word a:int64)`;`bit 2 (word a:int64)`;`bit 3 (word a:int64)`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let WORD_NEGMODINV_CORRECT = prove
 (`!a pc.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) word_negmodinv_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [a] s)
          (\s. read PC s = word(pc + 0x30) /\
               (ODD(val a)
                ==> (val a * val(C_RETURN s) + 1 == 0) (mod (2 EXP 64))))
             (MAYCHANGE [PC; X0; X1; X2] ,, MAYCHANGE [events])`,
  W64_GEN_TAC `a:num` THEN X_GEN_TAC `pc:num` THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN] THEN
  ENSURES_SEQUENCE_TAC `pc + 0xc`
    `\s. read X0 s = word a /\
         (ODD a ==> (a * val (read X1 s) + 1 == 0) (mod 16))` THEN
  CONJ_TAC THENL
   [ARM_SIM_TAC WORD_NEGMODINV_EXEC (1--3) THEN
    ASM_SIMP_TAC[WORD_NEGMODINV_SEED_LEMMA_16];
    GHOST_INTRO_TAC `x0:int64` `read X1` THEN
    ARM_SIM_TAC WORD_NEGMODINV_EXEC (1--9) THEN
    REWRITE_TAC[VAL_WORD_MUL; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
    SUBST1_TAC(ARITH_RULE `2 EXP 64 = 16 EXP (2 EXP 4)`) THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    SPEC_TAC(`16`,`e:num`) THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC NUMBER_RULE]);;

let WORD_NEGMODINV_SUBROUTINE_CORRECT = prove
 (`!a pc returnaddress.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) word_negmodinv_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [a] s)
          (\s. read PC s = returnaddress /\
               (ODD(val a)
                ==> (val a * val(C_RETURN s) + 1 == 0) (mod (2 EXP 64))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  ARM_ADD_RETURN_NOSTACK_TAC WORD_NEGMODINV_EXEC WORD_NEGMODINV_CORRECT);;
