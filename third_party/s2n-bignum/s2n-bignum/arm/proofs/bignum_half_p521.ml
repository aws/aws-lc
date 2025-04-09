(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Halving modulo p_521, the field characteristic for the NIST P-521 curve.  *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p521/bignum_half_p521.o";;
 ****)

let bignum_half_p521_mc = define_assert_from_elf "bignum_half_p521_mc" "arm/p521/bignum_half_p521.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0x92400046;       (* arm_AND X6 X2 (rvalue (word 1)) *)
  0x93c20462;       (* arm_EXTR X2 X3 X2 (rvalue (word 1)) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0x93c30483;       (* arm_EXTR X3 X4 X3 (rvalue (word 1)) *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0x93c404a4;       (* arm_EXTR X4 X5 X4 (rvalue (word 1)) *)
  0xa9420c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&32))) *)
  0x93c50445;       (* arm_EXTR X5 X2 X5 (rvalue (word 1)) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0x93c20462;       (* arm_EXTR X2 X3 X2 (rvalue (word 1)) *)
  0xa9431424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&48))) *)
  0x93c30483;       (* arm_EXTR X3 X4 X3 (rvalue (word 1)) *)
  0xa9020c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&32))) *)
  0x93c404a4;       (* arm_EXTR X4 X5 X4 (rvalue (word 1)) *)
  0xf9402022;       (* arm_LDR X2 X1 (Immediate_Offset (word 64)) *)
  0x93c50445;       (* arm_EXTR X5 X2 X5 (rvalue (word 1)) *)
  0xa9031404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&48))) *)
  0xd3492042;       (* arm_LSL X2 X2 (rvalue (word 55)) *)
  0x93c2e0c2;       (* arm_EXTR X2 X6 X2 (rvalue (word 56)) *)
  0xf9002002;       (* arm_STR X2 X0 (Immediate_Offset (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_HALF_P521_EXEC = ARM_MK_EXEC_RULE bignum_half_p521_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;

let P_521 = prove
 (`p_521 = 2 EXP 521 - 1`,
  REWRITE_TAC[p_521] THEN CONV_TAC NUM_REDUCE_CONV);;

let P_521_AS_WORDLIST = prove
 (`p_521 =
   bignum_of_wordlist
    [word_not(word 0);word_not(word 0);word_not(word 0);word_not(word 0);
     word_not(word 0);word_not(word 0);word_not(word 0);word_not(word 0);
     word(0x1FF)]`,
  REWRITE_TAC[p_521; bignum_of_wordlist] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_FROM_MEMORY_EQ_P521 = prove
 (`bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6;n7;n8] = p_521 <=>
   (!i. i < 64
        ==> bit i n0 /\ bit i n1 /\ bit i n2 /\ bit i n3 /\
            bit i n4 /\ bit i n5 /\ bit i n6 /\ bit i n7) /\
   (!i. i < 9 ==> bit i n8) /\ (!i. i < 64 ==> 9 <= i ==> ~bit i n8)`,
  REWRITE_TAC[P_521_AS_WORDLIST; BIGNUM_OF_WORDLIST_EQ] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC CONJ_ACI_RULE);;

let BIGNUM_FROM_MEMORY_LE_P521 = prove
 (`bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6;n7;n8] <= p_521 <=>
   !i. i < 64 ==> 9 <= i ==> ~bit i n8`,
  SIMP_TAC[P_521; ARITH_RULE `p_521 = 2 EXP 521 - 1 ==>
    (n <= p_521 <=> n DIV 2 EXP (8 * 64) < 2 EXP 9)`] THEN
  REWRITE_TAC[TOP_DEPTH_CONV num_CONV `8`; MULT_CLAUSES; EXP_ADD] THEN
  REWRITE_TAC[GSYM DIV_DIV; BIGNUM_OF_WORDLIST_DIV; EXP; DIV_1] THEN
  REWRITE_TAC[BIGNUM_OF_WORDLIST_SING; GSYM UPPER_BITS_ZERO] THEN
  MP_TAC(ISPEC `n8:int64` BIT_TRIVIAL) THEN REWRITE_TAC[DIMINDEX_64] THEN
  MESON_TAC[NOT_LE]);;

let BIGNUM_FROM_MEMORY_LT_P521 = prove
 (`bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6;n7;n8] < p_521 <=>
   (!i. i < 64 ==> 9 <= i ==> ~bit i n8) /\
   ~((!i. i < 64
          ==> bit i n0 /\ bit i n1 /\ bit i n2 /\ bit i n3 /\
              bit i n4 /\ bit i n5 /\ bit i n6 /\ bit i n7) /\
     (!i. i < 9 ==> bit i n8))`,
  GEN_REWRITE_TAC LAND_CONV [LT_LE] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_EQ_P521; BIGNUM_FROM_MEMORY_LE_P521] THEN
  MESON_TAC[]);;

let BIGNUM_HALF_P521_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x58) (z,8 * 9) /\
        (x = z \/ nonoverlapping(x,8 * 9) (z,8 * 9))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_half_p521_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = word (pc + 0x54) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s =
                       (inverse_mod p_521 2 * n) MOD p_521))
          (MAYCHANGE [PC; X2; X3; X4; X5; X6] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 9)) s0` THEN
  ARM_STEPS_TAC BIGNUM_HALF_P521_EXEC (1--21) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC[MOD_UNIQUE] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  UNDISCH_TAC `n < p_521` THEN EXPAND_TAC "n" THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_LT_P521; bignum_of_wordlist] THEN
  ASM_REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
   (LABEL_TAC "*" o CONV_RULE(RAND_CONV CONJ_CANON_CONV))) THEN
  REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
  REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
  REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
  REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_AND; BIT_WORD_1;
              BIT_WORD_SHL; DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV CONJ_CANON_CONV))) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(NUMBER_RULE
  `(2 * i == 1) (mod p) /\ (2 * x == n) (mod p) ==> (i * n == x) (mod p)`) THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_2; p_521] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_CONGRUENCE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  REAL_INTEGER_TAC);;

let BIGNUM_HALF_P521_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
        nonoverlapping (word pc,0x58) (z,8 * 9) /\
        (x = z \/ nonoverlapping(x,8 * 9) (z,8 * 9))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_half_p521_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = returnaddress /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s =
                       (inverse_mod p_521 2 * n) MOD p_521))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_HALF_P521_EXEC
    BIGNUM_HALF_P521_CORRECT);;
