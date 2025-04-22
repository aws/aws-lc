(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Big-endian transformation (byte reversal in this little-endian model).    *)
(* There are three different correctness variants corresponding to the three *)
(* aliases with different types (bigendian, frombebytes and tobebytes).      *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p384/bignum_bigendian_6.o";;
 ****)

let bignum_bigendian_6_mc =
  define_assert_from_elf "bignum_bigendian_6_mc" "arm/p384/bignum_bigendian_6.o"
[
  0x39401c22;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&7))) *)
  0x93df2043;       (* arm_EXTR X3 X2 XZR (rvalue (word 8)) *)
  0x39401822;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&6))) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 (rvalue (word 8)) *)
  0x39401422;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&5))) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 (rvalue (word 8)) *)
  0x39401022;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&4))) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 (rvalue (word 8)) *)
  0x39400c22;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&3))) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 (rvalue (word 8)) *)
  0x39400822;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&2))) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 (rvalue (word 8)) *)
  0x39400422;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&1))) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 (rvalue (word 8)) *)
  0x39400022;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&0))) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 (rvalue (word 8)) *)
  0x3940bc22;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&47))) *)
  0x93df2044;       (* arm_EXTR X4 X2 XZR (rvalue (word 8)) *)
  0x3940b822;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&46))) *)
  0x93c42044;       (* arm_EXTR X4 X2 X4 (rvalue (word 8)) *)
  0x3940b422;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&45))) *)
  0x93c42044;       (* arm_EXTR X4 X2 X4 (rvalue (word 8)) *)
  0x3940b022;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&44))) *)
  0x93c42044;       (* arm_EXTR X4 X2 X4 (rvalue (word 8)) *)
  0x3940ac22;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&43))) *)
  0x93c42044;       (* arm_EXTR X4 X2 X4 (rvalue (word 8)) *)
  0x3940a822;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&42))) *)
  0x93c42044;       (* arm_EXTR X4 X2 X4 (rvalue (word 8)) *)
  0x3940a422;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&41))) *)
  0x93c42044;       (* arm_EXTR X4 X2 X4 (rvalue (word 8)) *)
  0x3940a022;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&40))) *)
  0x93c42044;       (* arm_EXTR X4 X2 X4 (rvalue (word 8)) *)
  0xf9001403;       (* arm_STR X3 X0 (Immediate_Offset (word 40)) *)
  0xf9000004;       (* arm_STR X4 X0 (Immediate_Offset (word 0)) *)
  0x39403c22;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&15))) *)
  0x93df2043;       (* arm_EXTR X3 X2 XZR (rvalue (word 8)) *)
  0x39403822;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&14))) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 (rvalue (word 8)) *)
  0x39403422;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&13))) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 (rvalue (word 8)) *)
  0x39403022;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&12))) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 (rvalue (word 8)) *)
  0x39402c22;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&11))) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 (rvalue (word 8)) *)
  0x39402822;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&10))) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 (rvalue (word 8)) *)
  0x39402422;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&9))) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 (rvalue (word 8)) *)
  0x39402022;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&8))) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 (rvalue (word 8)) *)
  0x39409c22;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&39))) *)
  0x93df2044;       (* arm_EXTR X4 X2 XZR (rvalue (word 8)) *)
  0x39409822;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&38))) *)
  0x93c42044;       (* arm_EXTR X4 X2 X4 (rvalue (word 8)) *)
  0x39409422;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&37))) *)
  0x93c42044;       (* arm_EXTR X4 X2 X4 (rvalue (word 8)) *)
  0x39409022;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&36))) *)
  0x93c42044;       (* arm_EXTR X4 X2 X4 (rvalue (word 8)) *)
  0x39408c22;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&35))) *)
  0x93c42044;       (* arm_EXTR X4 X2 X4 (rvalue (word 8)) *)
  0x39408822;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&34))) *)
  0x93c42044;       (* arm_EXTR X4 X2 X4 (rvalue (word 8)) *)
  0x39408422;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&33))) *)
  0x93c42044;       (* arm_EXTR X4 X2 X4 (rvalue (word 8)) *)
  0x39408022;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&32))) *)
  0x93c42044;       (* arm_EXTR X4 X2 X4 (rvalue (word 8)) *)
  0xf9001003;       (* arm_STR X3 X0 (Immediate_Offset (word 32)) *)
  0xf9000404;       (* arm_STR X4 X0 (Immediate_Offset (word 8)) *)
  0x39405c22;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&23))) *)
  0x93df2043;       (* arm_EXTR X3 X2 XZR (rvalue (word 8)) *)
  0x39405822;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&22))) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 (rvalue (word 8)) *)
  0x39405422;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&21))) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 (rvalue (word 8)) *)
  0x39405022;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&20))) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 (rvalue (word 8)) *)
  0x39404c22;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&19))) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 (rvalue (word 8)) *)
  0x39404822;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&18))) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 (rvalue (word 8)) *)
  0x39404422;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&17))) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 (rvalue (word 8)) *)
  0x39404022;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&16))) *)
  0x93c32043;       (* arm_EXTR X3 X2 X3 (rvalue (word 8)) *)
  0x39407c22;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&31))) *)
  0x93df2044;       (* arm_EXTR X4 X2 XZR (rvalue (word 8)) *)
  0x39407822;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&30))) *)
  0x93c42044;       (* arm_EXTR X4 X2 X4 (rvalue (word 8)) *)
  0x39407422;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&29))) *)
  0x93c42044;       (* arm_EXTR X4 X2 X4 (rvalue (word 8)) *)
  0x39407022;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&28))) *)
  0x93c42044;       (* arm_EXTR X4 X2 X4 (rvalue (word 8)) *)
  0x39406c22;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&27))) *)
  0x93c42044;       (* arm_EXTR X4 X2 X4 (rvalue (word 8)) *)
  0x39406822;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&26))) *)
  0x93c42044;       (* arm_EXTR X4 X2 X4 (rvalue (word 8)) *)
  0x39406422;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&25))) *)
  0x93c42044;       (* arm_EXTR X4 X2 X4 (rvalue (word 8)) *)
  0x39406022;       (* arm_LDRB W2 X1 (Immediate_Offset (iword (&24))) *)
  0x93c42044;       (* arm_EXTR X4 X2 X4 (rvalue (word 8)) *)
  0xf9000c03;       (* arm_STR X3 X0 (Immediate_Offset (word 24)) *)
  0xf9000804;       (* arm_STR X4 X0 (Immediate_Offset (word 16)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_BIGENDIAN_6_EXEC = ARM_MK_EXEC_RULE bignum_bigendian_6_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof as a "frombebytes" function.                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_FROMBEBYTES_6_CORRECT = time prove
 (`!z x l pc.
      nonoverlapping (word pc,0x19c) (z,8 * 6) /\
      (x = z \/ nonoverlapping (x,8 * 6) (z,8 * 6))
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_bigendian_6_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [z; x] s /\
                read (memory :> bytelist(x,48)) s = l)
           (\s. read PC s = word (pc + 0x198) /\
                bignum_from_memory(z,6) s = num_of_bytelist (REVERSE l))
          (MAYCHANGE [PC; X2; X3; X4] ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `l:byte list`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BYTELIST_DIGITIZE_TAC "b_" `read (memory :> bytelist (x,48)) s0` THEN
  ARM_STEPS_TAC BIGNUM_BIGENDIAN_6_EXEC (1--102) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "l" THEN REWRITE_TAC[REVERSE; APPEND] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[num_of_bytelist] THEN
  CONV_TAC WORD_BLAST);;

let BIGNUM_FROMBEBYTES_6_SUBROUTINE_CORRECT = time prove
 (`!z x l pc returnaddress.
      nonoverlapping (word pc,0x19c) (z,8 * 6) /\
      (x = z \/ nonoverlapping (x,8 * 6) (z,8 * 6))
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_bigendian_6_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                read (memory :> bytelist(x,48)) s = l)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,6) s = num_of_bytelist (REVERSE l))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_BIGENDIAN_6_EXEC
    BIGNUM_FROMBEBYTES_6_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* As a "tobebytes" function.                                                *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_TOBEBYTES_6_CORRECT = time prove
 (`!z x n pc.
      nonoverlapping (word pc,0x19c) (z,8 * 6) /\
      (x = z \/ nonoverlapping (x,8 * 6) (z,8 * 6))
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_bigendian_6_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,6) s = n)
           (\s. read PC s = word (pc + 0x198) /\
                read (memory :> bytelist(z,48)) s =
                REVERSE(bytelist_of_num 48 n))
          (MAYCHANGE [PC; X2; X3; X4] ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ONCE_REWRITE_TAC[READ_BYTES_EQ_BYTELIST; READ_BYTELIST_EQ_BYTES] THEN
  REWRITE_TAC[LENGTH_REVERSE; LENGTH_BYTELIST_OF_NUM] THEN
  MP_TAC(ISPECL [`z:int64`; `x:int64`; `bytelist_of_num 48 n`; `pc:num`]
        BIGNUM_FROMBEBYTES_6_CORRECT) THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_PRECONDITION_THM) THEN
  SIMP_TAC[]);;

let BIGNUM_TOBEBYTES_6_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
      nonoverlapping (word pc,0x19c) (z,8 * 6) /\
      (x = z \/ nonoverlapping (x,8 * 6) (z,8 * 6))
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_bigendian_6_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,6) s = n)
           (\s. read PC s = returnaddress /\
                read (memory :> bytelist(z,48)) s =
                REVERSE(bytelist_of_num 48 n))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_BIGENDIAN_6_EXEC
    BIGNUM_TOBEBYTES_6_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* As a bignum-to-bignum operation.                                          *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_BIGENDIAN_6_CORRECT = time prove
 (`!z x n pc.
      nonoverlapping (word pc,0x19c) (z,8 * 6) /\
      (x = z \/ nonoverlapping (x,8 * 6) (z,8 * 6))
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_bigendian_6_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,6) s = n)
           (\s. read PC s = word (pc + 0x198) /\
                bignum_from_memory(z,6) s =
                num_of_bytelist(REVERSE(bytelist_of_num 48 n)))
          (MAYCHANGE [PC; X2; X3; X4] ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
        [BIGNUM_FROM_MEMORY_BYTES] THEN
  REWRITE_TAC[READ_BYTES_EQ_BYTELIST] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  MP_TAC(ISPECL [`z:int64`; `x:int64`; `bytelist_of_num 48 n`; `pc:num`]
        BIGNUM_FROMBEBYTES_6_CORRECT) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_PRECONDITION_THM) THEN
  SIMP_TAC[]);;

let BIGNUM_BIGENDIAN_6_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
      nonoverlapping (word pc,0x19c) (z,8 * 6) /\
      (x = z \/ nonoverlapping (x,8 * 6) (z,8 * 6))
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_bigendian_6_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,6) s = n)
           (\s. read PC s = returnaddress /\
                bignum_from_memory(z,6) s =
                num_of_bytelist(REVERSE(bytelist_of_num 48 n)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_BIGENDIAN_6_EXEC
    BIGNUM_BIGENDIAN_6_CORRECT);;
