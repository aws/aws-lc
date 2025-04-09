(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Translation to little-endian byte sequence, 9 digits -> 66 bytes.         *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p521/bignum_tolebytes_p521.o";;
 ****)

let bignum_tolebytes_p521_mc =
  define_assert_from_elf "bignum_tolebytes_p521_mc" "arm/p521/bignum_tolebytes_p521.o"
[
  0xf9400022;       (* arm_LDR X2 X1 (Immediate_Offset (word 0)) *)
  0x39000002;       (* arm_STRB W2 X0 (Immediate_Offset (word 0)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39000402;       (* arm_STRB W2 X0 (Immediate_Offset (word 1)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39000802;       (* arm_STRB W2 X0 (Immediate_Offset (word 2)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39000c02;       (* arm_STRB W2 X0 (Immediate_Offset (word 3)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39001002;       (* arm_STRB W2 X0 (Immediate_Offset (word 4)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39001402;       (* arm_STRB W2 X0 (Immediate_Offset (word 5)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39001802;       (* arm_STRB W2 X0 (Immediate_Offset (word 6)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39001c02;       (* arm_STRB W2 X0 (Immediate_Offset (word 7)) *)
  0xf9400422;       (* arm_LDR X2 X1 (Immediate_Offset (word 8)) *)
  0x39002002;       (* arm_STRB W2 X0 (Immediate_Offset (word 8)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39002402;       (* arm_STRB W2 X0 (Immediate_Offset (word 9)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39002802;       (* arm_STRB W2 X0 (Immediate_Offset (word 10)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39002c02;       (* arm_STRB W2 X0 (Immediate_Offset (word 11)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39003002;       (* arm_STRB W2 X0 (Immediate_Offset (word 12)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39003402;       (* arm_STRB W2 X0 (Immediate_Offset (word 13)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39003802;       (* arm_STRB W2 X0 (Immediate_Offset (word 14)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39003c02;       (* arm_STRB W2 X0 (Immediate_Offset (word 15)) *)
  0xf9400822;       (* arm_LDR X2 X1 (Immediate_Offset (word 16)) *)
  0x39004002;       (* arm_STRB W2 X0 (Immediate_Offset (word 16)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39004402;       (* arm_STRB W2 X0 (Immediate_Offset (word 17)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39004802;       (* arm_STRB W2 X0 (Immediate_Offset (word 18)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39004c02;       (* arm_STRB W2 X0 (Immediate_Offset (word 19)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39005002;       (* arm_STRB W2 X0 (Immediate_Offset (word 20)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39005402;       (* arm_STRB W2 X0 (Immediate_Offset (word 21)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39005802;       (* arm_STRB W2 X0 (Immediate_Offset (word 22)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39005c02;       (* arm_STRB W2 X0 (Immediate_Offset (word 23)) *)
  0xf9400c22;       (* arm_LDR X2 X1 (Immediate_Offset (word 24)) *)
  0x39006002;       (* arm_STRB W2 X0 (Immediate_Offset (word 24)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39006402;       (* arm_STRB W2 X0 (Immediate_Offset (word 25)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39006802;       (* arm_STRB W2 X0 (Immediate_Offset (word 26)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39006c02;       (* arm_STRB W2 X0 (Immediate_Offset (word 27)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39007002;       (* arm_STRB W2 X0 (Immediate_Offset (word 28)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39007402;       (* arm_STRB W2 X0 (Immediate_Offset (word 29)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39007802;       (* arm_STRB W2 X0 (Immediate_Offset (word 30)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39007c02;       (* arm_STRB W2 X0 (Immediate_Offset (word 31)) *)
  0xf9401022;       (* arm_LDR X2 X1 (Immediate_Offset (word 32)) *)
  0x39008002;       (* arm_STRB W2 X0 (Immediate_Offset (word 32)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39008402;       (* arm_STRB W2 X0 (Immediate_Offset (word 33)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39008802;       (* arm_STRB W2 X0 (Immediate_Offset (word 34)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39008c02;       (* arm_STRB W2 X0 (Immediate_Offset (word 35)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39009002;       (* arm_STRB W2 X0 (Immediate_Offset (word 36)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39009402;       (* arm_STRB W2 X0 (Immediate_Offset (word 37)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39009802;       (* arm_STRB W2 X0 (Immediate_Offset (word 38)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39009c02;       (* arm_STRB W2 X0 (Immediate_Offset (word 39)) *)
  0xf9401422;       (* arm_LDR X2 X1 (Immediate_Offset (word 40)) *)
  0x3900a002;       (* arm_STRB W2 X0 (Immediate_Offset (word 40)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x3900a402;       (* arm_STRB W2 X0 (Immediate_Offset (word 41)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x3900a802;       (* arm_STRB W2 X0 (Immediate_Offset (word 42)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x3900ac02;       (* arm_STRB W2 X0 (Immediate_Offset (word 43)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x3900b002;       (* arm_STRB W2 X0 (Immediate_Offset (word 44)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x3900b402;       (* arm_STRB W2 X0 (Immediate_Offset (word 45)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x3900b802;       (* arm_STRB W2 X0 (Immediate_Offset (word 46)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x3900bc02;       (* arm_STRB W2 X0 (Immediate_Offset (word 47)) *)
  0xf9401822;       (* arm_LDR X2 X1 (Immediate_Offset (word 48)) *)
  0x3900c002;       (* arm_STRB W2 X0 (Immediate_Offset (word 48)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x3900c402;       (* arm_STRB W2 X0 (Immediate_Offset (word 49)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x3900c802;       (* arm_STRB W2 X0 (Immediate_Offset (word 50)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x3900cc02;       (* arm_STRB W2 X0 (Immediate_Offset (word 51)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x3900d002;       (* arm_STRB W2 X0 (Immediate_Offset (word 52)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x3900d402;       (* arm_STRB W2 X0 (Immediate_Offset (word 53)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x3900d802;       (* arm_STRB W2 X0 (Immediate_Offset (word 54)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x3900dc02;       (* arm_STRB W2 X0 (Immediate_Offset (word 55)) *)
  0xf9401c22;       (* arm_LDR X2 X1 (Immediate_Offset (word 56)) *)
  0x3900e002;       (* arm_STRB W2 X0 (Immediate_Offset (word 56)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x3900e402;       (* arm_STRB W2 X0 (Immediate_Offset (word 57)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x3900e802;       (* arm_STRB W2 X0 (Immediate_Offset (word 58)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x3900ec02;       (* arm_STRB W2 X0 (Immediate_Offset (word 59)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x3900f002;       (* arm_STRB W2 X0 (Immediate_Offset (word 60)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x3900f402;       (* arm_STRB W2 X0 (Immediate_Offset (word 61)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x3900f802;       (* arm_STRB W2 X0 (Immediate_Offset (word 62)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x3900fc02;       (* arm_STRB W2 X0 (Immediate_Offset (word 63)) *)
  0xf9402022;       (* arm_LDR X2 X1 (Immediate_Offset (word 64)) *)
  0x39010002;       (* arm_STRB W2 X0 (Immediate_Offset (word 64)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39010402;       (* arm_STRB W2 X0 (Immediate_Offset (word 65)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_TOLEBYTES_P521_EXEC = ARM_MK_EXEC_RULE bignum_tolebytes_p521_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_TOLEBYTES_P521_CORRECT = time prove
 (`!z x n pc.
      nonoverlapping (word pc,0x214) (z,66) /\
      (x = z \/ nonoverlapping (x,8 * 9) (z,66))
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_tolebytes_p521_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,9) s = n)
           (\s. read PC s = word (pc + 0x210) /\
                read (memory :> bytelist(z,66)) s = bytelist_of_num 66 n)
          (MAYCHANGE [PC; X2] ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(z,66)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "d_" `bignum_from_memory(x,9) s0` THEN
  ARM_STEPS_TAC BIGNUM_TOLEBYTES_P521_EXEC (1--132) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[READ_BYTELIST_EQ_BYTES] THEN
  REWRITE_TAC[LENGTH_BYTELIST_OF_NUM; NUM_OF_BYTELIST_OF_NUM] THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[MOD_UNIQUE] THEN CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `256 EXP 66 = 2 EXP (8 * 66)`] THEN
    REWRITE_TAC[READ_BYTES_BOUND; READ_COMPONENT_COMPOSE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes (z,66)) s132 =
    read (memory :> bytes (z,64)) s132 +
    2 EXP (8 * 64) * read (memory :> bytes (word_add z (word 64),2)) s132`
  SUBST1_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; GSYM READ_BYTES_COMBINE] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REFL_TAC;
    REWRITE_TAC[SYM(NUM_MULT_CONV `8 * 8`)]] THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  REWRITE_TAC[READ_MEMORY_BYTESIZED_SPLIT] THEN
  CONV_TAC(RATOR_CONV(RAND_CONV(DEPTH_CONV
    NORMALIZE_RELATIVE_ADDRESS_CONV))) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "n" THEN
  REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[ARITH_RULE `256 EXP 66 = 2 EXP 512 * 2 EXP 16`] THEN
  MATCH_MP_TAC(NUMBER_RULE
   `a = b /\ (x:num == y) (mod d)
    ==> (a + e * x == b + e * y) (mod (e * d))`) THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[CONS_11] THEN REPEAT CONJ_TAC THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_64] THEN
    REWRITE_TAC[BIT_WORD_USHR; BIT_WORD_ZX; BIT_WORD_JOIN] THEN
    CONV_TAC(DEPTH_CONV(DIMINDEX_CONV ORELSEC NUM_RED_CONV)) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV;
    CONV_TAC(ONCE_DEPTH_CONV BYTES_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN
    MATCH_MP_TAC(MESON[CONG_REFL; CONG_LMOD]
     `x MOD n = y ==> (x == y) (mod n)`) THEN
    CONV_TAC WORD_BLAST]);;

let BIGNUM_TOLEBYTES_P521_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
      nonoverlapping (word pc,0x214) (z,66) /\
      (x = z \/ nonoverlapping (x,8 * 9) (z,66))
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_tolebytes_p521_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,9) s = n)
           (\s. read PC s = returnaddress /\
                read (memory :> bytelist(z,66)) s = bytelist_of_num 66 n)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,66)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_TOLEBYTES_P521_EXEC
    BIGNUM_TOLEBYTES_P521_CORRECT);;
