(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 6x6 -> 12 squaring, for uarchs with higher multiplier throughput.         *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/fastmul/bignum_sqr_6_12_alt.o";;
 ****)

let bignum_sqr_6_12_alt_mc = define_assert_from_elf "bignum_sqr_6_12_alt_mc" "arm/fastmul/bignum_sqr_6_12_alt.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0x9b047c48;       (* arm_MUL X8 X2 X4 *)
  0xab08014a;       (* arm_ADDS X10 X10 X8 *)
  0x9b057c4b;       (* arm_MUL X11 X2 X5 *)
  0x9b047c68;       (* arm_MUL X8 X3 X4 *)
  0xba08016b;       (* arm_ADCS X11 X11 X8 *)
  0x9bc57c4c;       (* arm_UMULH X12 X2 X5 *)
  0x9b057c68;       (* arm_MUL X8 X3 X5 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0xa9421c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&32))) *)
  0x9b077c4d;       (* arm_MUL X13 X2 X7 *)
  0x9b067c68;       (* arm_MUL X8 X3 X6 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9bc77c4e;       (* arm_UMULH X14 X2 X7 *)
  0x9b077c68;       (* arm_MUL X8 X3 X7 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9b067caf;       (* arm_MUL X15 X5 X6 *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0x9bc67cb0;       (* arm_UMULH X16 X5 X6 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0x9bc47c48;       (* arm_UMULH X8 X2 X4 *)
  0xab08016b;       (* arm_ADDS X11 X11 X8 *)
  0x9bc47c68;       (* arm_UMULH X8 X3 X4 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0x9bc57c68;       (* arm_UMULH X8 X3 X5 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9bc67c68;       (* arm_UMULH X8 X3 X6 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9bc77c68;       (* arm_UMULH X8 X3 X7 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0x9b067c48;       (* arm_MUL X8 X2 X6 *)
  0xab08018c;       (* arm_ADDS X12 X12 X8 *)
  0x9b057c88;       (* arm_MUL X8 X4 X5 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9b067c88;       (* arm_MUL X8 X4 X6 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9b077c88;       (* arm_MUL X8 X4 X7 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9b077ca8;       (* arm_MUL X8 X5 X7 *)
  0xba080210;       (* arm_ADCS X16 X16 X8 *)
  0x9b077cd1;       (* arm_MUL X17 X6 X7 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0x9bc77cd3;       (* arm_UMULH X19 X6 X7 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0x9bc67c48;       (* arm_UMULH X8 X2 X6 *)
  0xab0801ad;       (* arm_ADDS X13 X13 X8 *)
  0x9bc57c88;       (* arm_UMULH X8 X4 X5 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9bc67c88;       (* arm_UMULH X8 X4 X6 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9bc77c88;       (* arm_UMULH X8 X4 X7 *)
  0xba080210;       (* arm_ADCS X16 X16 X8 *)
  0x9bc77ca8;       (* arm_UMULH X8 X5 X7 *)
  0xba080231;       (* arm_ADCS X17 X17 X8 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0xab090129;       (* arm_ADDS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0x9a9f37f4;       (* arm_CSET X20 Condition_CS *)
  0x9bc27c48;       (* arm_UMULH X8 X2 X2 *)
  0x9b027c42;       (* arm_MUL X2 X2 X2 *)
  0xab080129;       (* arm_ADDS X9 X9 X8 *)
  0x9b037c68;       (* arm_MUL X8 X3 X3 *)
  0xba08014a;       (* arm_ADCS X10 X10 X8 *)
  0x9bc37c68;       (* arm_UMULH X8 X3 X3 *)
  0xba08016b;       (* arm_ADCS X11 X11 X8 *)
  0x9b047c88;       (* arm_MUL X8 X4 X4 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0x9bc47c88;       (* arm_UMULH X8 X4 X4 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9b057ca8;       (* arm_MUL X8 X5 X5 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9bc57ca8;       (* arm_UMULH X8 X5 X5 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9b067cc8;       (* arm_MUL X8 X6 X6 *)
  0xba080210;       (* arm_ADCS X16 X16 X8 *)
  0x9bc67cc8;       (* arm_UMULH X8 X6 X6 *)
  0xba080231;       (* arm_ADCS X17 X17 X8 *)
  0x9b077ce8;       (* arm_MUL X8 X7 X7 *)
  0xba080273;       (* arm_ADCS X19 X19 X8 *)
  0x9bc77ce8;       (* arm_UMULH X8 X7 X7 *)
  0x9a080294;       (* arm_ADC X20 X20 X8 *)
  0xa9002402;       (* arm_STP X2 X9 X0 (Immediate_Offset (iword (&0))) *)
  0xa9012c0a;       (* arm_STP X10 X11 X0 (Immediate_Offset (iword (&16))) *)
  0xa902340c;       (* arm_STP X12 X13 X0 (Immediate_Offset (iword (&32))) *)
  0xa9033c0e;       (* arm_STP X14 X15 X0 (Immediate_Offset (iword (&48))) *)
  0xa9044410;       (* arm_STP X16 X17 X0 (Immediate_Offset (iword (&64))) *)
  0xa9055013;       (* arm_STP X19 X20 X0 (Immediate_Offset (iword (&80))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_SQR_6_12_ALT_EXEC = ARM_MK_EXEC_RULE bignum_sqr_6_12_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_SQR_6_12_ALT_CORRECT = time prove
 (`!z x a pc.
     nonoverlapping (word pc,0x198) (z,8 * 12)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_sqr_6_12_alt_mc /\
               read PC s = word(pc + 0x4) /\
               C_ARGUMENTS [z; x] s /\
               bignum_from_memory (x,6) s = a)
          (\s. read PC s = word (pc + 0x190) /\
               bignum_from_memory (z,12) s = a EXP 2)
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9;
                      X10; X11; X12; X13; X14; X15; X16; X17; X19; X20] ,,
           MAYCHANGE [memory :> bytes(z,8 * 12)] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN
  ARM_ACCSTEPS_TAC BIGNUM_SQR_6_12_ALT_EXEC (1--99) (1--99) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_BITVAL; COND_SWAP]) THEN
  EXPAND_TAC "a" THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC);;

let BIGNUM_SQR_6_12_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
     aligned 16 stackpointer /\
     ALL (nonoverlapping (word_sub stackpointer (word 16),16))
         [(word pc,0x198); (z,8 * 12); (x,8 * 6)] /\
     nonoverlapping (word pc,0x198) (z,8 * 12)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_sqr_6_12_alt_mc /\
               read PC s = word pc /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [z; x] s /\
               bignum_from_memory (x,6) s = a)
          (\s. read PC s = returnaddress /\
               bignum_from_memory (z,12) s = a EXP 2)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * 12);
                       memory :> bytes(word_sub stackpointer (word 16),16)])`,
  ARM_ADD_RETURN_STACK_TAC
    BIGNUM_SQR_6_12_ALT_EXEC BIGNUM_SQR_6_12_ALT_CORRECT
    `[X19;X20]` 16);;
