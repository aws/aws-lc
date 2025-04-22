(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Mapping out of Montgomery representation modulo p_256k1.                  *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/secp256k1/bignum_demont_p256k1.o";;
 ****)

let bignum_demont_p256k1_mc =
  define_assert_from_elf "bignum_demont_p256k1_mc" "arm/secp256k1/bignum_demont_p256k1.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xd286a627;       (* arm_MOV X7 (rvalue (word 13617)) *)
  0xf2ba44a7;       (* arm_MOVK X7 (word 53797) 16 *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xf2c123a7;       (* arm_MOVK X7 (word 2333) 32 *)
  0xf2fb0707;       (* arm_MOVK X7 (word 55352) 48 *)
  0xd2807a28;       (* arm_MOV X8 (rvalue (word 977)) *)
  0xb2600108;       (* arm_ORR X8 X8 (rvalue (word 4294967296)) *)
  0x9b027ce2;       (* arm_MUL X2 X7 X2 *)
  0x9bc87c46;       (* arm_UMULH X6 X2 X8 *)
  0xeb060063;       (* arm_SUBS X3 X3 X6 *)
  0x9b037ce3;       (* arm_MUL X3 X7 X3 *)
  0x9bc87c66;       (* arm_UMULH X6 X3 X8 *)
  0xfa060084;       (* arm_SBCS X4 X4 X6 *)
  0x9b047ce4;       (* arm_MUL X4 X7 X4 *)
  0x9bc87c86;       (* arm_UMULH X6 X4 X8 *)
  0xfa0600a5;       (* arm_SBCS X5 X5 X6 *)
  0x9b057ce5;       (* arm_MUL X5 X7 X5 *)
  0x9bc87ca6;       (* arm_UMULH X6 X5 X8 *)
  0xfa060042;       (* arm_SBCS X2 X2 X6 *)
  0xfa1f0063;       (* arm_SBCS X3 X3 XZR *)
  0xfa1f0084;       (* arm_SBCS X4 X4 XZR *)
  0xda1f00a5;       (* arm_SBC X5 X5 XZR *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_DEMONT_P256K1_EXEC = ARM_MK_EXEC_RULE bignum_demont_p256k1_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256k1 = new_definition `p_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`;;

let mmlemma = prove
 (`!h (l:int64) (x:int64).
        &2 pow 64 * &h + &(val(l:int64)):real =
        &(val(word(15580212934572586289 * val(x:int64)):int64)) * &4294968273
        ==> &2 pow 64 * &h + &(val(x:int64)):real =
            &(val(word(15580212934572586289 * val(x:int64)):int64)) *
            &4294968273`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; DIMINDEX_64] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
   MATCH_MP (NUMBER_RULE
    `p * h + l:num = y ==> (y == x) (mod p) ==> (x == l) (mod p)`)) THEN
  REWRITE_TAC[CONG; VAL_WORD; VAL_WORD_MUL; DIMINDEX_64] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(a * b == 1) (mod p) ==> ((a * x) * b == x) (mod p)`) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_DEMONT_P256K1_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x68) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_demont_p256k1_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + 0x64) /\
                  (a < p_256k1
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256k1 (2 EXP 256) * a) MOD p_256k1))
             (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  ARM_ACCSTEPS_TAC BIGNUM_DEMONT_P256K1_EXEC
   [10;11;13;14;16;17;19;20;21;22;23] (1--25) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN

  (*** Do the congruential reasoning on the chosen multipliers ***)

  RULE_ASSUM_TAC(fun th -> try MATCH_MP mmlemma th with Failure _ -> th) THEN

  (*** Now finish the proof directly ***)

  MATCH_MP_TAC(MESON[]
   `(2 EXP 256 * t <= (2 EXP 256 - 1) * p_256k1 + a /\
     (2 EXP 256 * t == a) (mod p_256k1)
     ==> t = (inverse_mod p_256k1 (2 EXP 256) * a) MOD p_256k1) /\
    2 EXP 256 * t <= (2 EXP 256 - 1) * p_256k1 + a /\
    (2 EXP 256 * t == a) (mod p_256k1)
    ==> t = (inverse_mod p_256k1 (2 EXP 256) * a) MOD p_256k1`) THEN
  CONJ_TAC THENL
   [STRIP_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC[MOD_UNIQUE] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM NOT_LT]) THEN
      UNDISCH_TAC `a < p_256k1` THEN REWRITE_TAC[p_256k1] THEN ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP(NUMBER_RULE
       `(e * t == a) (mod p)
        ==> (e * i == 1) (mod p) ==> (i * a == t) (mod p)`)) THEN
      REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
      REWRITE_TAC[p_256k1] THEN CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  EXPAND_TAC "a" THEN
  REWRITE_TAC[REAL_CONGRUENCE; GSYM REAL_OF_NUM_CLAUSES; p_256k1] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_EQ_CONV) THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a:real <= b + c <=> a - c <= b`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; REAL_INTEGER_TAC]);;

let BIGNUM_DEMONT_P256K1_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,0x68) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_demont_p256k1_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = returnaddress /\
                  (a < p_256k1
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256k1 (2 EXP 256) * a) MOD p_256k1))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC
    BIGNUM_DEMONT_P256K1_EXEC BIGNUM_DEMONT_P256K1_CORRECT);;
