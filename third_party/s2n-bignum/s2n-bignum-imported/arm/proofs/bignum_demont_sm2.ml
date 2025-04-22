(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Mapping out of Montgomery representation modulo p_sm2.                    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/sm2/bignum_demont_sm2.o";;
 ****)

let bignum_demont_sm2_mc =
  define_assert_from_elf "bignum_demont_sm2_mc" "arm/sm2/bignum_demont_sm2.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xd3607c47;       (* arm_LSL X7 X2 32 *)
  0xd360fc46;       (* arm_LSR X6 X2 32 *)
  0xeb0200e9;       (* arm_SUBS X9 X7 X2 *)
  0xda1f00c8;       (* arm_SBC X8 X6 XZR *)
  0xeb090063;       (* arm_SUBS X3 X3 X9 *)
  0xfa080084;       (* arm_SBCS X4 X4 X8 *)
  0xfa0700a5;       (* arm_SBCS X5 X5 X7 *)
  0xda060042;       (* arm_SBC X2 X2 X6 *)
  0xd3607c67;       (* arm_LSL X7 X3 32 *)
  0xd360fc66;       (* arm_LSR X6 X3 32 *)
  0xeb0300e9;       (* arm_SUBS X9 X7 X3 *)
  0xda1f00c8;       (* arm_SBC X8 X6 XZR *)
  0xeb090084;       (* arm_SUBS X4 X4 X9 *)
  0xfa0800a5;       (* arm_SBCS X5 X5 X8 *)
  0xfa070042;       (* arm_SBCS X2 X2 X7 *)
  0xda060063;       (* arm_SBC X3 X3 X6 *)
  0xd3607c87;       (* arm_LSL X7 X4 32 *)
  0xd360fc86;       (* arm_LSR X6 X4 32 *)
  0xeb0400e9;       (* arm_SUBS X9 X7 X4 *)
  0xda1f00c8;       (* arm_SBC X8 X6 XZR *)
  0xeb0900a5;       (* arm_SUBS X5 X5 X9 *)
  0xfa080042;       (* arm_SBCS X2 X2 X8 *)
  0xfa070063;       (* arm_SBCS X3 X3 X7 *)
  0xda060084;       (* arm_SBC X4 X4 X6 *)
  0xd3607ca7;       (* arm_LSL X7 X5 32 *)
  0xd360fca6;       (* arm_LSR X6 X5 32 *)
  0xeb0500e9;       (* arm_SUBS X9 X7 X5 *)
  0xda1f00c8;       (* arm_SBC X8 X6 XZR *)
  0xeb090042;       (* arm_SUBS X2 X2 X9 *)
  0xfa080063;       (* arm_SBCS X3 X3 X8 *)
  0xfa070084;       (* arm_SBCS X4 X4 X7 *)
  0xda0600a5;       (* arm_SBC X5 X5 X6 *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_DEMONT_SM2_EXEC = ARM_MK_EXEC_RULE bignum_demont_sm2_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_sm2 = new_definition `p_sm2 = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF`;;

let BIGNUM_DEMONT_SM2_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x94) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_demont_sm2_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + 0x90) /\
                  (a < p_sm2
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_sm2 (2 EXP 256) * a) MOD p_sm2))
             (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  ARM_ACCSTEPS_TAC BIGNUM_DEMONT_SM2_EXEC (1--36) (1--36) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `(2 EXP 256 * t <= (2 EXP 256 - 1) * p_sm2 + a /\
     (2 EXP 256 * t == a) (mod p_sm2)
     ==> t = (inverse_mod p_sm2 (2 EXP 256) * a) MOD p_sm2) /\
    2 EXP 256 * t <= (2 EXP 256 - 1) * p_sm2 + a /\
    (2 EXP 256 * t == a) (mod p_sm2)
    ==> t = (inverse_mod p_sm2 (2 EXP 256) * a) MOD p_sm2`) THEN
  CONJ_TAC THENL
   [STRIP_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC[MOD_UNIQUE] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM NOT_LT]) THEN
      UNDISCH_TAC `a < p_sm2` THEN REWRITE_TAC[p_sm2] THEN ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP(NUMBER_RULE
       `(e * t == a) (mod p)
        ==> (e * i == 1) (mod p) ==> (i * a == t) (mod p)`)) THEN
      REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
      REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  EXPAND_TAC "a" THEN
  REWRITE_TAC[REAL_CONGRUENCE; GSYM REAL_OF_NUM_CLAUSES; p_sm2] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_EQ_CONV) THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a:real <= b + c <=> a - c <= b`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; REAL_INTEGER_TAC]);;

let BIGNUM_DEMONT_SM2_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,0x94) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_demont_sm2_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = returnaddress /\
                  (a < p_sm2
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_sm2 (2 EXP 256) * a) MOD p_sm2))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_DEMONT_SM2_EXEC
    BIGNUM_DEMONT_SM2_CORRECT);;
