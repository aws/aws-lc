(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 4x4->8 squaring optimized for uarchs with higher multiplier throughput.   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/fastmul/bignum_sqr_4_8_alt.o";;
 ****)

let bignum_sqr_4_8_alt_mc =
  define_assert_from_elf "bignum_sqr_4_8_alt_mc" "arm/fastmul/bignum_sqr_4_8_alt.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0x9b057c4b;       (* arm_MUL X11 X2 X5 *)
  0x9bc57c4c;       (* arm_UMULH X12 X2 X5 *)
  0x9b047c46;       (* arm_MUL X6 X2 X4 *)
  0x9bc47c47;       (* arm_UMULH X7 X2 X4 *)
  0xab06014a;       (* arm_ADDS X10 X10 X6 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9b047c66;       (* arm_MUL X6 X3 X4 *)
  0x9bc47c67;       (* arm_UMULH X7 X3 X4 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xab06016b;       (* arm_ADDS X11 X11 X6 *)
  0x9b057c8d;       (* arm_MUL X13 X4 X5 *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xba07018c;       (* arm_ADCS X12 X12 X7 *)
  0x9b057c66;       (* arm_MUL X6 X3 X5 *)
  0x9bc57c67;       (* arm_UMULH X7 X3 X5 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xab06018c;       (* arm_ADDS X12 X12 X6 *)
  0xba0701ad;       (* arm_ADCS X13 X13 X7 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab090129;       (* arm_ADDS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0x9a9f37e7;       (* arm_CSET X7 Condition_CS *)
  0x9bc27c46;       (* arm_UMULH X6 X2 X2 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
  0xab060129;       (* arm_ADDS X9 X9 X6 *)
  0x9b037c66;       (* arm_MUL X6 X3 X3 *)
  0xba06014a;       (* arm_ADCS X10 X10 X6 *)
  0x9bc37c66;       (* arm_UMULH X6 X3 X3 *)
  0xba06016b;       (* arm_ADCS X11 X11 X6 *)
  0x9b047c86;       (* arm_MUL X6 X4 X4 *)
  0xba06018c;       (* arm_ADCS X12 X12 X6 *)
  0x9bc47c86;       (* arm_UMULH X6 X4 X4 *)
  0xba0601ad;       (* arm_ADCS X13 X13 X6 *)
  0x9b057ca6;       (* arm_MUL X6 X5 X5 *)
  0xba0601ce;       (* arm_ADCS X14 X14 X6 *)
  0x9bc57ca6;       (* arm_UMULH X6 X5 X5 *)
  0x9a0600e7;       (* arm_ADC X7 X7 X6 *)
  0xa9002408;       (* arm_STP X8 X9 X0 (Immediate_Offset (iword (&0))) *)
  0xa9012c0a;       (* arm_STP X10 X11 X0 (Immediate_Offset (iword (&16))) *)
  0xa902340c;       (* arm_STP X12 X13 X0 (Immediate_Offset (iword (&32))) *)
  0xa9031c0e;       (* arm_STP X14 X7 X0 (Immediate_Offset (iword (&48))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_SQR_4_8_ALT_EXEC = ARM_MK_EXEC_RULE bignum_sqr_4_8_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_SQR_4_8_ALT_CORRECT = time prove
 (`!z x a pc.
     nonoverlapping (word pc,0xc8) (z,8 * 8)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_sqr_4_8_alt_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [z; x] s /\
               bignum_from_memory (x,4) s = a)
          (\s. read PC s = word (pc + 0xc4) /\
               bignum_from_memory (z,8) s = a EXP 2)
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9;
                      X10; X11; X12; X13; X14] ,,
           MAYCHANGE [memory :> bytes(z,8 * 8)] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN
  ARM_ACCSTEPS_TAC BIGNUM_SQR_4_8_ALT_EXEC (1--49) (1--49) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_BITVAL; COND_SWAP]) THEN
  EXPAND_TAC "a" THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC);;

let BIGNUM_SQR_4_8_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
     nonoverlapping (word pc,0xc8) (z,8 * 8)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_sqr_4_8_alt_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [z; x] s /\
               bignum_from_memory (x,4) s = a)
          (\s. read PC s = returnaddress /\
               bignum_from_memory (z,8) s = a EXP 2)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * 8)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_SQR_4_8_ALT_EXEC
    BIGNUM_SQR_4_8_ALT_CORRECT);;
