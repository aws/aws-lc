(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 6x6->12 multiply optimized for uarchs with higher multiplier throughput.  *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/fastmul/bignum_mul_6_12_alt.o";;
 ****)

let bignum_mul_6_12_alt_mc =
  define_assert_from_elf "bignum_mul_6_12_alt_mc" "arm/fastmul/bignum_mul_6_12_alt.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0xa9401845;       (* arm_LDP X5 X6 X2 (Immediate_Offset (iword (&0))) *)
  0x9b057c6c;       (* arm_MUL X12 X3 X5 *)
  0x9bc57c6d;       (* arm_UMULH X13 X3 X5 *)
  0x9b067c6b;       (* arm_MUL X11 X3 X6 *)
  0x9bc67c6e;       (* arm_UMULH X14 X3 X6 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9412047;       (* arm_LDP X7 X8 X2 (Immediate_Offset (iword (&16))) *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9bc77c6f;       (* arm_UMULH X15 X3 X7 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c70;       (* arm_UMULH X16 X3 X8 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0xa9422849;       (* arm_LDP X9 X10 X2 (Immediate_Offset (iword (&32))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c71;       (* arm_UMULH X17 X3 X9 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c73;       (* arm_UMULH X19 X3 X10 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0x9b057c8b;       (* arm_MUL X11 X4 X5 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0x9b067c8b;       (* arm_MUL X11 X4 X6 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b077c8b;       (* arm_MUL X11 X4 X7 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9b087c8b;       (* arm_MUL X11 X4 X8 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b097c8b;       (* arm_MUL X11 X4 X9 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9b0a7c8b;       (* arm_MUL X11 X4 X10 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9a9f37f4;       (* arm_CSET X20 Condition_CS *)
  0x9bc57c8b;       (* arm_UMULH X11 X4 X5 *)
  0xab0b01ce;       (* arm_ADDS X14 X14 X11 *)
  0x9bc67c8b;       (* arm_UMULH X11 X4 X6 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9bc77c8b;       (* arm_UMULH X11 X4 X7 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9bc87c8b;       (* arm_UMULH X11 X4 X8 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9bc97c8b;       (* arm_UMULH X11 X4 X9 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9bca7c8b;       (* arm_UMULH X11 X4 X10 *)
  0x9a0b0294;       (* arm_ADC X20 X20 X11 *)
  0xa900340c;       (* arm_STP X12 X13 X0 (Immediate_Offset (iword (&0))) *)
  0xa9411023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&16))) *)
  0x9b057c6b;       (* arm_MUL X11 X3 X5 *)
  0xab0b01ce;       (* arm_ADDS X14 X14 X11 *)
  0x9b067c6b;       (* arm_MUL X11 X3 X6 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9a9f37ec;       (* arm_CSET X12 Condition_CS *)
  0x9bc57c6b;       (* arm_UMULH X11 X3 X5 *)
  0xab0b01ef;       (* arm_ADDS X15 X15 X11 *)
  0x9bc67c6b;       (* arm_UMULH X11 X3 X6 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9bc77c6b;       (* arm_UMULH X11 X3 X7 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9bc87c6b;       (* arm_UMULH X11 X3 X8 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9bc97c6b;       (* arm_UMULH X11 X3 X9 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9bca7c6b;       (* arm_UMULH X11 X3 X10 *)
  0x9a0b018c;       (* arm_ADC X12 X12 X11 *)
  0x9b057c8b;       (* arm_MUL X11 X4 X5 *)
  0xab0b01ef;       (* arm_ADDS X15 X15 X11 *)
  0x9b067c8b;       (* arm_MUL X11 X4 X6 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b077c8b;       (* arm_MUL X11 X4 X7 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9b087c8b;       (* arm_MUL X11 X4 X8 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9b097c8b;       (* arm_MUL X11 X4 X9 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9b0a7c8b;       (* arm_MUL X11 X4 X10 *)
  0xba0b018c;       (* arm_ADCS X12 X12 X11 *)
  0x9a9f37ed;       (* arm_CSET X13 Condition_CS *)
  0x9bc57c8b;       (* arm_UMULH X11 X4 X5 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc67c8b;       (* arm_UMULH X11 X4 X6 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9bc77c8b;       (* arm_UMULH X11 X4 X7 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9bc87c8b;       (* arm_UMULH X11 X4 X8 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9bc97c8b;       (* arm_UMULH X11 X4 X9 *)
  0xba0b018c;       (* arm_ADCS X12 X12 X11 *)
  0x9bca7c8b;       (* arm_UMULH X11 X4 X10 *)
  0x9a0b01ad;       (* arm_ADC X13 X13 X11 *)
  0xa9013c0e;       (* arm_STP X14 X15 X0 (Immediate_Offset (iword (&16))) *)
  0xa9421023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&32))) *)
  0x9b057c6b;       (* arm_MUL X11 X3 X5 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9b067c6b;       (* arm_MUL X11 X3 X6 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0xba0b018c;       (* arm_ADCS X12 X12 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9a9f37ee;       (* arm_CSET X14 Condition_CS *)
  0x9bc57c6b;       (* arm_UMULH X11 X3 X5 *)
  0xab0b0231;       (* arm_ADDS X17 X17 X11 *)
  0x9bc67c6b;       (* arm_UMULH X11 X3 X6 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9bc77c6b;       (* arm_UMULH X11 X3 X7 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9bc87c6b;       (* arm_UMULH X11 X3 X8 *)
  0xba0b018c;       (* arm_ADCS X12 X12 X11 *)
  0x9bc97c6b;       (* arm_UMULH X11 X3 X9 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9bca7c6b;       (* arm_UMULH X11 X3 X10 *)
  0x9a0b01ce;       (* arm_ADC X14 X14 X11 *)
  0x9b057c8b;       (* arm_MUL X11 X4 X5 *)
  0xab0b0231;       (* arm_ADDS X17 X17 X11 *)
  0x9b067c8b;       (* arm_MUL X11 X4 X6 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9b077c8b;       (* arm_MUL X11 X4 X7 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9b087c8b;       (* arm_MUL X11 X4 X8 *)
  0xba0b018c;       (* arm_ADCS X12 X12 X11 *)
  0x9b097c8b;       (* arm_MUL X11 X4 X9 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b0a7c8b;       (* arm_MUL X11 X4 X10 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9a9f37ef;       (* arm_CSET X15 Condition_CS *)
  0x9bc57c8b;       (* arm_UMULH X11 X4 X5 *)
  0xab0b0273;       (* arm_ADDS X19 X19 X11 *)
  0x9bc67c8b;       (* arm_UMULH X11 X4 X6 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9bc77c8b;       (* arm_UMULH X11 X4 X7 *)
  0xba0b018c;       (* arm_ADCS X12 X12 X11 *)
  0x9bc87c8b;       (* arm_UMULH X11 X4 X8 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9bc97c8b;       (* arm_UMULH X11 X4 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9bca7c8b;       (* arm_UMULH X11 X4 X10 *)
  0x9a0b01ef;       (* arm_ADC X15 X15 X11 *)
  0xa9024410;       (* arm_STP X16 X17 X0 (Immediate_Offset (iword (&32))) *)
  0xa9035013;       (* arm_STP X19 X20 X0 (Immediate_Offset (iword (&48))) *)
  0xa904340c;       (* arm_STP X12 X13 X0 (Immediate_Offset (iword (&64))) *)
  0xa9053c0e;       (* arm_STP X14 X15 X0 (Immediate_Offset (iword (&80))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MUL_6_12_ALT_EXEC = ARM_MK_EXEC_RULE bignum_mul_6_12_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MUL_6_12_ALT_CORRECT = time prove
 (`!z x y a b pc.
     nonoverlapping (word pc,0x278) (z,8 * 12) /\
     (x = z \/ nonoverlapping (x,8 * 6) (z,8 * 12))
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_mul_6_12_alt_mc /\
               read PC s = word(pc + 0x4) /\
               C_ARGUMENTS [z; x; y] s /\
               bignum_from_memory (x,6) s = a /\
               bignum_from_memory (y,6) s = b)
          (\s. read PC s = word (pc + 0x270) /\
               bignum_from_memory (z,12) s = a * b)
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9;
                      X10; X11; X12; X13; X14; X15; X16; X17; X19; X20] ,,
           MAYCHANGE [memory :> bytes(z,8 * 12)] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN
  BIGNUM_DIGITIZE_TAC "y_" `bignum_from_memory (y,6) s0` THEN
  ARM_ACCSTEPS_TAC BIGNUM_MUL_6_12_ALT_EXEC (1--155) (1--155) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC);;

let BIGNUM_MUL_6_12_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc stackpointer returnaddress.
     aligned 16 stackpointer /\
     nonoverlapping (z,8 * 12) (word_sub stackpointer (word 16),16) /\
     (x = z \/ nonoverlapping (x,8 * 6) (z,8 * 12)) /\
     ALLPAIRS nonoverlapping
          [(z,8 * 12); (word_sub stackpointer (word 16),16)]
          [(word pc,0x278); (x,8 * 6); (y,8 * 6)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_mul_6_12_alt_mc /\
               read PC s = word pc /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [z; x; y] s /\
               bignum_from_memory (x,6) s = a /\
               bignum_from_memory (y,6) s = b)
          (\s. read PC s = returnaddress /\
               bignum_from_memory (z,12) s = a * b)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * 12);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  ARM_ADD_RETURN_STACK_TAC
    BIGNUM_MUL_6_12_ALT_EXEC BIGNUM_MUL_6_12_ALT_CORRECT
    `[X19;X20]` 16);;
