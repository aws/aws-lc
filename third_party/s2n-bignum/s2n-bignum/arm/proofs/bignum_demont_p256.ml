(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Mapping out of Montgomery representation modulo p_256.                    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p256/bignum_demont_p256.o";;
 ****)

let bignum_demont_p256_mc =
  define_assert_from_elf "bignum_demont_p256_mc" "arm/p256/bignum_demont_p256.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xd3607c47;       (* arm_LSL X7 X2 (rvalue (word 32)) *)
  0xeb070048;       (* arm_SUBS X8 X2 X7 *)
  0xd360fc46;       (* arm_LSR X6 X2 (rvalue (word 32)) *)
  0xda060042;       (* arm_SBC X2 X2 X6 *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba060084;       (* arm_ADCS X4 X4 X6 *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0x9a1f0042;       (* arm_ADC X2 X2 XZR *)
  0xd3607c67;       (* arm_LSL X7 X3 (rvalue (word 32)) *)
  0xeb070068;       (* arm_SUBS X8 X3 X7 *)
  0xd360fc66;       (* arm_LSR X6 X3 (rvalue (word 32)) *)
  0xda060063;       (* arm_SBC X3 X3 X6 *)
  0xab070084;       (* arm_ADDS X4 X4 X7 *)
  0xba0600a5;       (* arm_ADCS X5 X5 X6 *)
  0xba080042;       (* arm_ADCS X2 X2 X8 *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0xd3607c87;       (* arm_LSL X7 X4 (rvalue (word 32)) *)
  0xeb070088;       (* arm_SUBS X8 X4 X7 *)
  0xd360fc86;       (* arm_LSR X6 X4 (rvalue (word 32)) *)
  0xda060084;       (* arm_SBC X4 X4 X6 *)
  0xab0700a5;       (* arm_ADDS X5 X5 X7 *)
  0xba060042;       (* arm_ADCS X2 X2 X6 *)
  0xba080063;       (* arm_ADCS X3 X3 X8 *)
  0x9a1f0084;       (* arm_ADC X4 X4 XZR *)
  0xd3607ca7;       (* arm_LSL X7 X5 (rvalue (word 32)) *)
  0xeb0700a8;       (* arm_SUBS X8 X5 X7 *)
  0xd360fca6;       (* arm_LSR X6 X5 (rvalue (word 32)) *)
  0xda0600a5;       (* arm_SBC X5 X5 X6 *)
  0xab070042;       (* arm_ADDS X2 X2 X7 *)
  0xba060063;       (* arm_ADCS X3 X3 X6 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_DEMONT_P256_EXEC = ARM_MK_EXEC_RULE bignum_demont_p256_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256 = new_definition `p_256 = 115792089210356248762697446949407573530086143415290314195533631308867097853951`;;

let BIGNUM_DEMONT_P256_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x94) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_demont_p256_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + 0x90) /\
                  (a < p_256
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256 (2 EXP 256) * a) MOD p_256))
             (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  ARM_ACCSTEPS_TAC BIGNUM_DEMONT_P256_EXEC (1--36) (1--36) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `(2 EXP 256 * t <= (2 EXP 256 - 1) * p_256 + a /\
     (2 EXP 256 * t == a) (mod p_256)
     ==> t = (inverse_mod p_256 (2 EXP 256) * a) MOD p_256) /\
    2 EXP 256 * t <= (2 EXP 256 - 1) * p_256 + a /\
    (2 EXP 256 * t == a) (mod p_256)
    ==> t = (inverse_mod p_256 (2 EXP 256) * a) MOD p_256`) THEN
  CONJ_TAC THENL
   [STRIP_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC[MOD_UNIQUE] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM NOT_LT]) THEN
      UNDISCH_TAC `a < p_256` THEN REWRITE_TAC[p_256] THEN ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP(NUMBER_RULE
       `(e * t == a) (mod p)
        ==> (e * i == 1) (mod p) ==> (i * a == t) (mod p)`)) THEN
      REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
      REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  EXPAND_TAC "a" THEN
  REWRITE_TAC[REAL_CONGRUENCE; GSYM REAL_OF_NUM_CLAUSES; p_256] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_EQ_CONV) THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a:real <= b + c <=> a - c <= b`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; REAL_INTEGER_TAC]);;

let BIGNUM_DEMONT_P256_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,0x94) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_demont_p256_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = returnaddress /\
                  (a < p_256
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256 (2 EXP 256) * a) MOD p_256))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_DEMONT_P256_EXEC
    BIGNUM_DEMONT_P256_CORRECT);;
