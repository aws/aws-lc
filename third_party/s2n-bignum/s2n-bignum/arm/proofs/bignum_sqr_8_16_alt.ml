(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 8x8 -> 16 squaring, for uarchs with higher multiplier throughput.         *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/fastmul/bignum_sqr_8_16_alt.o";;
 ****)

let bignum_sqr_8_16_alt_mc = define_assert_from_elf "bignum_sqr_8_16_alt_mc" "arm/fastmul/bignum_sqr_8_16_alt.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf6bf9;       (* arm_STP X25 X26 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0x9b037c4b;       (* arm_MUL X11 X2 X3 *)
  0x9bc37c4c;       (* arm_UMULH X12 X2 X3 *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0x9b047c4a;       (* arm_MUL X10 X2 X4 *)
  0x9bc47c4d;       (* arm_UMULH X13 X2 X4 *)
  0xab0a018c;       (* arm_ADDS X12 X12 X10 *)
  0xa9421c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&32))) *)
  0x9b057c4a;       (* arm_MUL X10 X2 X5 *)
  0x9bc57c4e;       (* arm_UMULH X14 X2 X5 *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0xa9432428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&48))) *)
  0x9b067c4a;       (* arm_MUL X10 X2 X6 *)
  0x9bc67c4f;       (* arm_UMULH X15 X2 X6 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x9b077c4a;       (* arm_MUL X10 X2 X7 *)
  0x9bc77c50;       (* arm_UMULH X16 X2 X7 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9b087c4a;       (* arm_MUL X10 X2 X8 *)
  0x9bc87c51;       (* arm_UMULH X17 X2 X8 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9b097c4a;       (* arm_MUL X10 X2 X9 *)
  0x9bc97c53;       (* arm_UMULH X19 X2 X9 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0x9b047c6a;       (* arm_MUL X10 X3 X4 *)
  0xab0a01ad;       (* arm_ADDS X13 X13 X10 *)
  0x9b057c6a;       (* arm_MUL X10 X3 X5 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x9b067c6a;       (* arm_MUL X10 X3 X6 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9b077c6a;       (* arm_MUL X10 X3 X7 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9b087c6a;       (* arm_MUL X10 X3 X8 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9b097c6a;       (* arm_MUL X10 X3 X9 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9a9f37f4;       (* arm_CSET X20 Condition_CS *)
  0x9bc47c6a;       (* arm_UMULH X10 X3 X4 *)
  0xab0a01ce;       (* arm_ADDS X14 X14 X10 *)
  0x9bc57c6a;       (* arm_UMULH X10 X3 X5 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9bc67c6a;       (* arm_UMULH X10 X3 X6 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9bc77c6a;       (* arm_UMULH X10 X3 X7 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9bc87c6a;       (* arm_UMULH X10 X3 X8 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9bc97c6a;       (* arm_UMULH X10 X3 X9 *)
  0x9a0a0294;       (* arm_ADC X20 X20 X10 *)
  0x9b077cca;       (* arm_MUL X10 X6 X7 *)
  0x9bc77cd5;       (* arm_UMULH X21 X6 X7 *)
  0xab0a0294;       (* arm_ADDS X20 X20 X10 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0x9b057c8a;       (* arm_MUL X10 X4 X5 *)
  0xab0a01ef;       (* arm_ADDS X15 X15 X10 *)
  0x9b067c8a;       (* arm_MUL X10 X4 X6 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9b077c8a;       (* arm_MUL X10 X4 X7 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9b087c8a;       (* arm_MUL X10 X4 X8 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9b097c8a;       (* arm_MUL X10 X4 X9 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b087cca;       (* arm_MUL X10 X6 X8 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9a9f37f6;       (* arm_CSET X22 Condition_CS *)
  0x9bc57c8a;       (* arm_UMULH X10 X4 X5 *)
  0xab0a0210;       (* arm_ADDS X16 X16 X10 *)
  0x9bc67c8a;       (* arm_UMULH X10 X4 X6 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9bc77c8a;       (* arm_UMULH X10 X4 X7 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9bc87c8a;       (* arm_UMULH X10 X4 X8 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9bc97c8a;       (* arm_UMULH X10 X4 X9 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc87cca;       (* arm_UMULH X10 X6 X8 *)
  0x9a0a02d6;       (* arm_ADC X22 X22 X10 *)
  0x9b087cea;       (* arm_MUL X10 X7 X8 *)
  0x9bc87cf7;       (* arm_UMULH X23 X7 X8 *)
  0xab0a02d6;       (* arm_ADDS X22 X22 X10 *)
  0x9a1f02f7;       (* arm_ADC X23 X23 XZR *)
  0x9b067caa;       (* arm_MUL X10 X5 X6 *)
  0xab0a0231;       (* arm_ADDS X17 X17 X10 *)
  0x9b077caa;       (* arm_MUL X10 X5 X7 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9b087caa;       (* arm_MUL X10 X5 X8 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b097caa;       (* arm_MUL X10 X5 X9 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9b097cca;       (* arm_MUL X10 X6 X9 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9b097cea;       (* arm_MUL X10 X7 X9 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9a9f37f8;       (* arm_CSET X24 Condition_CS *)
  0x9bc67caa;       (* arm_UMULH X10 X5 X6 *)
  0xab0a0273;       (* arm_ADDS X19 X19 X10 *)
  0x9bc77caa;       (* arm_UMULH X10 X5 X7 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9bc87caa;       (* arm_UMULH X10 X5 X8 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc97caa;       (* arm_UMULH X10 X5 X9 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9bc97cca;       (* arm_UMULH X10 X6 X9 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9bc97cea;       (* arm_UMULH X10 X7 X9 *)
  0x9a0a0318;       (* arm_ADC X24 X24 X10 *)
  0x9b097d0a;       (* arm_MUL X10 X8 X9 *)
  0x9bc97d19;       (* arm_UMULH X25 X8 X9 *)
  0xab0a0318;       (* arm_ADDS X24 X24 X10 *)
  0x9a1f0339;       (* arm_ADC X25 X25 XZR *)
  0xab0b016b;       (* arm_ADDS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0xba140294;       (* arm_ADCS X20 X20 X20 *)
  0xba1502b5;       (* arm_ADCS X21 X21 X21 *)
  0xba1602d6;       (* arm_ADCS X22 X22 X22 *)
  0xba1702f7;       (* arm_ADCS X23 X23 X23 *)
  0xba180318;       (* arm_ADCS X24 X24 X24 *)
  0xba190339;       (* arm_ADCS X25 X25 X25 *)
  0x9a9f37fa;       (* arm_CSET X26 Condition_CS *)
  0x9bc27c4a;       (* arm_UMULH X10 X2 X2 *)
  0x9b027c42;       (* arm_MUL X2 X2 X2 *)
  0xab0a016b;       (* arm_ADDS X11 X11 X10 *)
  0x9b037c6a;       (* arm_MUL X10 X3 X3 *)
  0xba0a018c;       (* arm_ADCS X12 X12 X10 *)
  0x9bc37c6a;       (* arm_UMULH X10 X3 X3 *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x9b047c8a;       (* arm_MUL X10 X4 X4 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x9bc47c8a;       (* arm_UMULH X10 X4 X4 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9b057caa;       (* arm_MUL X10 X5 X5 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9bc57caa;       (* arm_UMULH X10 X5 X5 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9b067cca;       (* arm_MUL X10 X6 X6 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9bc67cca;       (* arm_UMULH X10 X6 X6 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b077cea;       (* arm_MUL X10 X7 X7 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc77cea;       (* arm_UMULH X10 X7 X7 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9b087d0a;       (* arm_MUL X10 X8 X8 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9bc87d0a;       (* arm_UMULH X10 X8 X8 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9b097d2a;       (* arm_MUL X10 X9 X9 *)
  0xba0a0339;       (* arm_ADCS X25 X25 X10 *)
  0x9bc97d2a;       (* arm_UMULH X10 X9 X9 *)
  0x9a0a035a;       (* arm_ADC X26 X26 X10 *)
  0xa9002c02;       (* arm_STP X2 X11 X0 (Immediate_Offset (iword (&0))) *)
  0xa901340c;       (* arm_STP X12 X13 X0 (Immediate_Offset (iword (&16))) *)
  0xa9023c0e;       (* arm_STP X14 X15 X0 (Immediate_Offset (iword (&32))) *)
  0xa9034410;       (* arm_STP X16 X17 X0 (Immediate_Offset (iword (&48))) *)
  0xa9045013;       (* arm_STP X19 X20 X0 (Immediate_Offset (iword (&64))) *)
  0xa9055815;       (* arm_STP X21 X22 X0 (Immediate_Offset (iword (&80))) *)
  0xa9066017;       (* arm_STP X23 X24 X0 (Immediate_Offset (iword (&96))) *)
  0xa9076819;       (* arm_STP X25 X26 X0 (Immediate_Offset (iword (&112))) *)
  0xa8c16bf9;       (* arm_LDP X25 X26 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_SQR_8_16_ALT_EXEC = ARM_MK_EXEC_RULE bignum_sqr_8_16_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_SQR_8_16_ALT_CORRECT = time prove
 (`!z x a pc.
     nonoverlapping (word pc,0x2bc) (z,8 * 16)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_sqr_8_16_alt_mc /\
               read PC s = word(pc + 0x10) /\
               C_ARGUMENTS [z; x] s /\
               bignum_from_memory (x,8) s = a)
          (\s. read PC s = word (pc + 0x2a8) /\
               bignum_from_memory (z,16) s = a EXP 2)
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9;
                      X10; X11; X12; X13; X14; X15; X16; X17; X19;
                      X20; X21; X22; X23; X24; X25; X26] ,,
           MAYCHANGE [memory :> bytes(z,8 * 16)] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,8) s0` THEN
  ARM_ACCSTEPS_TAC BIGNUM_SQR_8_16_ALT_EXEC (1--166) (1--166) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_BITVAL; COND_SWAP]) THEN
  EXPAND_TAC "a" THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC);;

let BIGNUM_SQR_8_16_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
     aligned 16 stackpointer /\
     ALL (nonoverlapping (word_sub stackpointer (word 64),64))
         [(word pc,0x2bc); (z,8 * 16); (x,8 * 8)] /\
     nonoverlapping (word pc,0x2bc) (z,8 * 16)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_sqr_8_16_alt_mc /\
               read PC s = word pc /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [z; x] s /\
               bignum_from_memory (x,8) s = a)
          (\s. read PC s = returnaddress /\
               bignum_from_memory (z,16) s = a EXP 2)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * 16);
                       memory :> bytes(word_sub stackpointer (word 64),64)])`,
  ARM_ADD_RETURN_STACK_TAC
    BIGNUM_SQR_8_16_ALT_EXEC BIGNUM_SQR_8_16_ALT_CORRECT
    `[X19;X20;X21;X22;X23;X24;X25;X26]` 64);;
