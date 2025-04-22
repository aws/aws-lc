(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Translation from little-endian byte sequence, 66 bytes -> 9 digits.       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p521/bignum_fromlebytes_p521.o";;
 ****)

let bignum_fromlebytes_p521_mc =
  define_assert_from_elf "bignum_fromlebytes_p521_mc" "arm/p521/bignum_fromlebytes_p521.o"
[
  0x39400022;       (* arm_LDRB W2 X1 (Immediate_Offset (word 0)) *)
  0x93df2043;       (* arm_EXTR X3 X2 XZR 8 *)
  0x39400422;       (* arm_LDRB W2 X1 (Immediate_Offset (word 1)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39400822;       (* arm_LDRB W2 X1 (Immediate_Offset (word 2)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39400c22;       (* arm_LDRB W2 X1 (Immediate_Offset (word 3)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39401022;       (* arm_LDRB W2 X1 (Immediate_Offset (word 4)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39401422;       (* arm_LDRB W2 X1 (Immediate_Offset (word 5)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39401822;       (* arm_LDRB W2 X1 (Immediate_Offset (word 6)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39401c22;       (* arm_LDRB W2 X1 (Immediate_Offset (word 7)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0xf9000003;       (* arm_STR X3 X0 (Immediate_Offset (word 0)) *)
  0x39402022;       (* arm_LDRB W2 X1 (Immediate_Offset (word 8)) *)
  0x93df2043;       (* arm_EXTR X3 X2 XZR 8 *)
  0x39402422;       (* arm_LDRB W2 X1 (Immediate_Offset (word 9)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39402822;       (* arm_LDRB W2 X1 (Immediate_Offset (word 10)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39402c22;       (* arm_LDRB W2 X1 (Immediate_Offset (word 11)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39403022;       (* arm_LDRB W2 X1 (Immediate_Offset (word 12)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39403422;       (* arm_LDRB W2 X1 (Immediate_Offset (word 13)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39403822;       (* arm_LDRB W2 X1 (Immediate_Offset (word 14)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39403c22;       (* arm_LDRB W2 X1 (Immediate_Offset (word 15)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0xf9000403;       (* arm_STR X3 X0 (Immediate_Offset (word 8)) *)
  0x39404022;       (* arm_LDRB W2 X1 (Immediate_Offset (word 16)) *)
  0x93df2043;       (* arm_EXTR X3 X2 XZR 8 *)
  0x39404422;       (* arm_LDRB W2 X1 (Immediate_Offset (word 17)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39404822;       (* arm_LDRB W2 X1 (Immediate_Offset (word 18)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39404c22;       (* arm_LDRB W2 X1 (Immediate_Offset (word 19)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39405022;       (* arm_LDRB W2 X1 (Immediate_Offset (word 20)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39405422;       (* arm_LDRB W2 X1 (Immediate_Offset (word 21)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39405822;       (* arm_LDRB W2 X1 (Immediate_Offset (word 22)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39405c22;       (* arm_LDRB W2 X1 (Immediate_Offset (word 23)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0xf9000803;       (* arm_STR X3 X0 (Immediate_Offset (word 16)) *)
  0x39406022;       (* arm_LDRB W2 X1 (Immediate_Offset (word 24)) *)
  0x93df2043;       (* arm_EXTR X3 X2 XZR 8 *)
  0x39406422;       (* arm_LDRB W2 X1 (Immediate_Offset (word 25)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39406822;       (* arm_LDRB W2 X1 (Immediate_Offset (word 26)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39406c22;       (* arm_LDRB W2 X1 (Immediate_Offset (word 27)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39407022;       (* arm_LDRB W2 X1 (Immediate_Offset (word 28)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39407422;       (* arm_LDRB W2 X1 (Immediate_Offset (word 29)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39407822;       (* arm_LDRB W2 X1 (Immediate_Offset (word 30)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39407c22;       (* arm_LDRB W2 X1 (Immediate_Offset (word 31)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0xf9000c03;       (* arm_STR X3 X0 (Immediate_Offset (word 24)) *)
  0x39408022;       (* arm_LDRB W2 X1 (Immediate_Offset (word 32)) *)
  0x93df2043;       (* arm_EXTR X3 X2 XZR 8 *)
  0x39408422;       (* arm_LDRB W2 X1 (Immediate_Offset (word 33)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39408822;       (* arm_LDRB W2 X1 (Immediate_Offset (word 34)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39408c22;       (* arm_LDRB W2 X1 (Immediate_Offset (word 35)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39409022;       (* arm_LDRB W2 X1 (Immediate_Offset (word 36)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39409422;       (* arm_LDRB W2 X1 (Immediate_Offset (word 37)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39409822;       (* arm_LDRB W2 X1 (Immediate_Offset (word 38)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x39409c22;       (* arm_LDRB W2 X1 (Immediate_Offset (word 39)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0xf9001003;       (* arm_STR X3 X0 (Immediate_Offset (word 32)) *)
  0x3940a022;       (* arm_LDRB W2 X1 (Immediate_Offset (word 40)) *)
  0x93df2043;       (* arm_EXTR X3 X2 XZR 8 *)
  0x3940a422;       (* arm_LDRB W2 X1 (Immediate_Offset (word 41)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x3940a822;       (* arm_LDRB W2 X1 (Immediate_Offset (word 42)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x3940ac22;       (* arm_LDRB W2 X1 (Immediate_Offset (word 43)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x3940b022;       (* arm_LDRB W2 X1 (Immediate_Offset (word 44)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x3940b422;       (* arm_LDRB W2 X1 (Immediate_Offset (word 45)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x3940b822;       (* arm_LDRB W2 X1 (Immediate_Offset (word 46)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x3940bc22;       (* arm_LDRB W2 X1 (Immediate_Offset (word 47)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0xf9001403;       (* arm_STR X3 X0 (Immediate_Offset (word 40)) *)
  0x3940c022;       (* arm_LDRB W2 X1 (Immediate_Offset (word 48)) *)
  0x93df2043;       (* arm_EXTR X3 X2 XZR 8 *)
  0x3940c422;       (* arm_LDRB W2 X1 (Immediate_Offset (word 49)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x3940c822;       (* arm_LDRB W2 X1 (Immediate_Offset (word 50)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x3940cc22;       (* arm_LDRB W2 X1 (Immediate_Offset (word 51)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x3940d022;       (* arm_LDRB W2 X1 (Immediate_Offset (word 52)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x3940d422;       (* arm_LDRB W2 X1 (Immediate_Offset (word 53)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x3940d822;       (* arm_LDRB W2 X1 (Immediate_Offset (word 54)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x3940dc22;       (* arm_LDRB W2 X1 (Immediate_Offset (word 55)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0xf9001803;       (* arm_STR X3 X0 (Immediate_Offset (word 48)) *)
  0x3940e022;       (* arm_LDRB W2 X1 (Immediate_Offset (word 56)) *)
  0x93df2043;       (* arm_EXTR X3 X2 XZR 8 *)
  0x3940e422;       (* arm_LDRB W2 X1 (Immediate_Offset (word 57)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x3940e822;       (* arm_LDRB W2 X1 (Immediate_Offset (word 58)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x3940ec22;       (* arm_LDRB W2 X1 (Immediate_Offset (word 59)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x3940f022;       (* arm_LDRB W2 X1 (Immediate_Offset (word 60)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x3940f422;       (* arm_LDRB W2 X1 (Immediate_Offset (word 61)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x3940f822;       (* arm_LDRB W2 X1 (Immediate_Offset (word 62)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0x3940fc22;       (* arm_LDRB W2 X1 (Immediate_Offset (word 63)) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 8 *)
  0xf9001c03;       (* arm_STR X3 X0 (Immediate_Offset (word 56)) *)
  0x39410022;       (* arm_LDRB W2 X1 (Immediate_Offset (word 64)) *)
  0x93df2043;       (* arm_EXTR X3 X2 XZR 8 *)
  0x39410422;       (* arm_LDRB W2 X1 (Immediate_Offset (word 65)) *)
  0x93c3e043;       (* arm_EXTR X3 X2 X3 56 *)
  0xf9002003;       (* arm_STR X3 X0 (Immediate_Offset (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_FROMLEBYTES_P521_EXEC = ARM_MK_EXEC_RULE bignum_fromlebytes_p521_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_FROMLEBYTES_P521_CORRECT = time prove
 (`!z x l pc.
      nonoverlapping (word pc,0x238) (z,8 * 9) /\
      (x = z \/ nonoverlapping (x,66) (z,8 * 9))
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_fromlebytes_p521_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [z; x] s /\
                read (memory :> bytelist(x,66)) s = l)
           (\s. read PC s = word (pc + 0x234) /\
                bignum_from_memory(z,9) s = num_of_bytelist l)
          (MAYCHANGE [PC; X2; X3] ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `l:byte list`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BYTELIST_DIGITIZE_TAC "b_" `read (memory :> bytelist (x,66)) s0` THEN
  ARM_STEPS_TAC BIGNUM_FROMLEBYTES_P521_EXEC (1--141) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "l" THEN REWRITE_TAC[num_of_bytelist] THEN CONV_TAC WORD_BLAST);;

let BIGNUM_FROMLEBYTES_P521_SUBROUTINE_CORRECT = time prove
 (`!z x l pc returnaddress.
      nonoverlapping (word pc,0x238) (z,8 * 9) /\
      (x = z \/ nonoverlapping (x,66) (z,8 * 9))
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_fromlebytes_p521_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                read (memory :> bytelist(x,66)) s = l)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,9) s = num_of_bytelist l)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_FROMLEBYTES_P521_EXEC
    BIGNUM_FROMLEBYTES_P521_CORRECT);;
