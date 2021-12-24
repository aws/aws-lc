(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 *)

(* ========================================================================= *)
(* 4x4->8 multiply optimized for uarchs with higher multiplier throughput.   *)
(* ========================================================================= *)

(**** print_literal_from_elf "arm/fastmul/bignum_mul_4_8_alt.o";;
 ****)

let bignum_mul_4_8_alt_mc =
  define_assert_from_elf "bignum_mul_4_8_alt_mc" "arm/fastmul/bignum_mul_4_8_alt.o"
[
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0xa9402047;       (* arm_LDP X7 X8 X2 (Immediate_Offset (iword (&0))) *)
  0x9b077c6d;       (* arm_MUL X13 X3 X7 *)
  0x9bc77c6e;       (* arm_UMULH X14 X3 X7 *)
  0x9b087c6c;       (* arm_MUL X12 X3 X8 *)
  0x9bc87c6f;       (* arm_UMULH X15 X3 X8 *)
  0xab0c01ce;       (* arm_ADDS X14 X14 X12 *)
  0xa9412849;       (* arm_LDP X9 X10 X2 (Immediate_Offset (iword (&16))) *)
  0x9b097c6c;       (* arm_MUL X12 X3 X9 *)
  0x9bc97c70;       (* arm_UMULH X16 X3 X9 *)
  0xba0c01ef;       (* arm_ADCS X15 X15 X12 *)
  0x9b0a7c6c;       (* arm_MUL X12 X3 X10 *)
  0x9bca7c63;       (* arm_UMULH X3 X3 X10 *)
  0xba0c0210;       (* arm_ADCS X16 X16 X12 *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0xa9411825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&16))) *)
  0x9b077c8c;       (* arm_MUL X12 X4 X7 *)
  0x9bc77c8b;       (* arm_UMULH X11 X4 X7 *)
  0xab0c01ce;       (* arm_ADDS X14 X14 X12 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9b087c8c;       (* arm_MUL X12 X4 X8 *)
  0x9bc87c8b;       (* arm_UMULH X11 X4 X8 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c01ef;       (* arm_ADDS X15 X15 X12 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b097c8c;       (* arm_MUL X12 X4 X9 *)
  0x9bc97c8b;       (* arm_UMULH X11 X4 X9 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0210;       (* arm_ADDS X16 X16 X12 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9b0a7c8c;       (* arm_MUL X12 X4 X10 *)
  0x9bca7c8b;       (* arm_UMULH X11 X4 X10 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0063;       (* arm_ADDS X3 X3 X12 *)
  0x9a1f0164;       (* arm_ADC X4 X11 XZR *)
  0x9b077cac;       (* arm_MUL X12 X5 X7 *)
  0x9bc77cab;       (* arm_UMULH X11 X5 X7 *)
  0xab0c01ef;       (* arm_ADDS X15 X15 X12 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b087cac;       (* arm_MUL X12 X5 X8 *)
  0x9bc87cab;       (* arm_UMULH X11 X5 X8 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0210;       (* arm_ADDS X16 X16 X12 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9b097cac;       (* arm_MUL X12 X5 X9 *)
  0x9bc97cab;       (* arm_UMULH X11 X5 X9 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0063;       (* arm_ADDS X3 X3 X12 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9b0a7cac;       (* arm_MUL X12 X5 X10 *)
  0x9bca7cab;       (* arm_UMULH X11 X5 X10 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0084;       (* arm_ADDS X4 X4 X12 *)
  0x9a1f0165;       (* arm_ADC X5 X11 XZR *)
  0x9b077ccc;       (* arm_MUL X12 X6 X7 *)
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0c0210;       (* arm_ADDS X16 X16 X12 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9b087ccc;       (* arm_MUL X12 X6 X8 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0063;       (* arm_ADDS X3 X3 X12 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9b097ccc;       (* arm_MUL X12 X6 X9 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0084;       (* arm_ADDS X4 X4 X12 *)
  0xba0b00a5;       (* arm_ADCS X5 X5 X11 *)
  0x9b0a7ccc;       (* arm_MUL X12 X6 X10 *)
  0x9bca7ccb;       (* arm_UMULH X11 X6 X10 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c00a5;       (* arm_ADDS X5 X5 X12 *)
  0x9a1f0166;       (* arm_ADC X6 X11 XZR *)
  0xa900380d;       (* arm_STP X13 X14 X0 (Immediate_Offset (iword (&0))) *)
  0xa901400f;       (* arm_STP X15 X16 X0 (Immediate_Offset (iword (&16))) *)
  0xa9021003;       (* arm_STP X3 X4 X0 (Immediate_Offset (iword (&32))) *)
  0xa9031805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&48))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MUL_4_8_ALT_EXEC = ARM_MK_EXEC_RULE bignum_mul_4_8_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MUL_4_8_ALT_CORRECT = time prove
 (`!z x y a b pc.
     nonoverlapping (word pc,0x138) (z,8 * 8)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_mul_4_8_alt_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [z; x; y] s /\
               bignum_from_memory (x,4) s = a /\
               bignum_from_memory (y,4) s = b)
          (\s. read PC s = word (pc + 0x134) /\
               bignum_from_memory (z,8) s = a * b)
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9;
                      X10; X11; X12; X13; X14; X15; X16] ,,
           MAYCHANGE [memory :> bytes(z,8 * 8)] ,,
           MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN
  BIGNUM_DIGITIZE_TAC "y_" `bignum_from_memory (y,4) s0` THEN
  ARM_ACCSTEPS_TAC BIGNUM_MUL_4_8_ALT_EXEC (1--77) (1--77) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC);;

let BIGNUM_MUL_4_8_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc returnaddress.
     nonoverlapping (word pc,0x138) (z,8 * 8)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_mul_4_8_alt_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [z; x; y] s /\
               bignum_from_memory (x,4) s = a /\
               bignum_from_memory (y,4) s = b)
          (\s. read PC s = returnaddress /\
               bignum_from_memory (z,8) s = a * b)
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9;
                      X10; X11; X12; X13; X14; X15; X16] ,,
           MAYCHANGE [memory :> bytes(z,8 * 8)] ,,
           MAYCHANGE SOME_FLAGS)`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MUL_4_8_ALT_EXEC
     BIGNUM_MUL_4_8_ALT_CORRECT);;
