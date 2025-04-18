(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Encoding of point on edwards25519 in its compressed form.                 *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/ecencoding.ml";;

(**** print_literal_from_elf "arm/curve25519/edwards25519_encode.o";;
 ****)

let edwards25519_encode_mc =
  define_assert_from_elf "edwards25519_encode_mc" "arm/curve25519/edwards25519_encode.o"
[
  0xf9400026;       (* arm_LDR X6 X1 (Immediate_Offset (word 0)) *)
  0xa9420c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&32))) *)
  0xa9431424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&48))) *)
  0x9240f8a5;       (* arm_AND X5 X5 (rvalue (word 9223372036854775807)) *)
  0xaa06fca5;       (* arm_ORR X5 X5 (Shiftedreg X6 LSL 63) *)
  0x39000002;       (* arm_STRB W2 X0 (Immediate_Offset (word 0)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39000402;       (* arm_STRB W2 X0 (Immediate_Offset (word 1)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39000802;       (* arm_STRB W2 X0 (Immediate_Offset (word 2)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39000c02;       (* arm_STRB W2 X0 (Immediate_Offset (word 3)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39001002;       (* arm_STRB W2 X0 (Immediate_Offset (word 4)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39001402;       (* arm_STRB W2 X0 (Immediate_Offset (word 5)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39001802;       (* arm_STRB W2 X0 (Immediate_Offset (word 6)) *)
  0xd348fc42;       (* arm_LSR X2 X2 8 *)
  0x39001c02;       (* arm_STRB W2 X0 (Immediate_Offset (word 7)) *)
  0x39002003;       (* arm_STRB W3 X0 (Immediate_Offset (word 8)) *)
  0xd348fc63;       (* arm_LSR X3 X3 8 *)
  0x39002403;       (* arm_STRB W3 X0 (Immediate_Offset (word 9)) *)
  0xd348fc63;       (* arm_LSR X3 X3 8 *)
  0x39002803;       (* arm_STRB W3 X0 (Immediate_Offset (word 10)) *)
  0xd348fc63;       (* arm_LSR X3 X3 8 *)
  0x39002c03;       (* arm_STRB W3 X0 (Immediate_Offset (word 11)) *)
  0xd348fc63;       (* arm_LSR X3 X3 8 *)
  0x39003003;       (* arm_STRB W3 X0 (Immediate_Offset (word 12)) *)
  0xd348fc63;       (* arm_LSR X3 X3 8 *)
  0x39003403;       (* arm_STRB W3 X0 (Immediate_Offset (word 13)) *)
  0xd348fc63;       (* arm_LSR X3 X3 8 *)
  0x39003803;       (* arm_STRB W3 X0 (Immediate_Offset (word 14)) *)
  0xd348fc63;       (* arm_LSR X3 X3 8 *)
  0x39003c03;       (* arm_STRB W3 X0 (Immediate_Offset (word 15)) *)
  0x39004004;       (* arm_STRB W4 X0 (Immediate_Offset (word 16)) *)
  0xd348fc84;       (* arm_LSR X4 X4 8 *)
  0x39004404;       (* arm_STRB W4 X0 (Immediate_Offset (word 17)) *)
  0xd348fc84;       (* arm_LSR X4 X4 8 *)
  0x39004804;       (* arm_STRB W4 X0 (Immediate_Offset (word 18)) *)
  0xd348fc84;       (* arm_LSR X4 X4 8 *)
  0x39004c04;       (* arm_STRB W4 X0 (Immediate_Offset (word 19)) *)
  0xd348fc84;       (* arm_LSR X4 X4 8 *)
  0x39005004;       (* arm_STRB W4 X0 (Immediate_Offset (word 20)) *)
  0xd348fc84;       (* arm_LSR X4 X4 8 *)
  0x39005404;       (* arm_STRB W4 X0 (Immediate_Offset (word 21)) *)
  0xd348fc84;       (* arm_LSR X4 X4 8 *)
  0x39005804;       (* arm_STRB W4 X0 (Immediate_Offset (word 22)) *)
  0xd348fc84;       (* arm_LSR X4 X4 8 *)
  0x39005c04;       (* arm_STRB W4 X0 (Immediate_Offset (word 23)) *)
  0x39006005;       (* arm_STRB W5 X0 (Immediate_Offset (word 24)) *)
  0xd348fca5;       (* arm_LSR X5 X5 8 *)
  0x39006405;       (* arm_STRB W5 X0 (Immediate_Offset (word 25)) *)
  0xd348fca5;       (* arm_LSR X5 X5 8 *)
  0x39006805;       (* arm_STRB W5 X0 (Immediate_Offset (word 26)) *)
  0xd348fca5;       (* arm_LSR X5 X5 8 *)
  0x39006c05;       (* arm_STRB W5 X0 (Immediate_Offset (word 27)) *)
  0xd348fca5;       (* arm_LSR X5 X5 8 *)
  0x39007005;       (* arm_STRB W5 X0 (Immediate_Offset (word 28)) *)
  0xd348fca5;       (* arm_LSR X5 X5 8 *)
  0x39007405;       (* arm_STRB W5 X0 (Immediate_Offset (word 29)) *)
  0xd348fca5;       (* arm_LSR X5 X5 8 *)
  0x39007805;       (* arm_STRB W5 X0 (Immediate_Offset (word 30)) *)
  0xd348fca5;       (* arm_LSR X5 X5 8 *)
  0x39007c05;       (* arm_STRB W5 X0 (Immediate_Offset (word 31)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let EDWARDS25519_ENCODE_EXEC = ARM_MK_EXEC_RULE edwards25519_encode_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_25519 = define `p_25519 = 57896044618658097711785492504343953926634992332820282019728792003956564819949`;;

let ed25519_encode = new_definition
  `ed25519_encode (X,Y) =
        let x = num_of_int(X rem &p_25519)
        and y = num_of_int(Y rem &p_25519) in
        2 EXP 255 * x MOD 2 + y`;;

let EDWARDS25519_ENCODE_CORRECT = time prove
 (`!z p x y pc.
      nonoverlapping (word pc,0x108) (z,32)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) edwards25519_encode_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [z; p] s /\
                bignum_pair_from_memory(p,4) s = (x,y))
           (\s. read PC s = word (pc + 0x104) /\
                (x < p_25519 /\ y < p_25519
                ==> read (memory :> bytelist(z,32)) s =
                    bytelist_of_num 32 (ed25519_encode (&x,&y))))
          (MAYCHANGE [PC; X2; X3; X4; X5; X6] ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(z,32)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `p:int64`; `x:num`; `y:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              PAIR_EQ; bignum_pair_from_memory] THEN
  STRIP_TAC THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "x_" `read (memory :> bytes (p,8 * 4)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "y_"
   `read (memory :> bytes (word_add p (word 32),8 * 4)) s0` THEN
  ARM_STEPS_TAC EDWARDS25519_ENCODE_EXEC (1--65) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN REWRITE_TAC[READ_BYTELIST_EQ_BYTES] THEN
  REWRITE_TAC[LENGTH_BYTELIST_OF_NUM; NUM_OF_BYTELIST_OF_NUM] THEN
  MATCH_MP_TAC(MESON[MOD_LT] `x < e /\ x = y ==> x = y MOD e`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `256 EXP 32 = 2 EXP (8 * 32)`] THEN
    REWRITE_TAC[READ_BYTES_BOUND; READ_COMPONENT_COMPOSE];
    CONV_TAC(LAND_CONV BYTES_EXPAND_CONV) THEN ASM_REWRITE_TAC[]] THEN
  DISCARD_STATE_TAC "s65" THEN
  ASM_SIMP_TAC[ed25519_encode; INT_OF_NUM_REM; MOD_LT; NUM_OF_INT_OF_NUM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `y = y MOD 2 EXP 255` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `y < p_25519` THEN REWRITE_TAC[p_25519] THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXPAND_TAC ["x"; "y"] THEN
  REWRITE_TAC[ARITH_RULE
   `z = x + y MOD 2 EXP 255 <=>
    2 EXP 255 * y DIV 2 EXP 255 + z = x + y`] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
  REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(1,3)] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 64 * x = 2 * 2 EXP 63 * x`; MOD_MULT_ADD] THEN
  REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN
  REWRITE_TAC[bignum_of_wordlist] THEN
  CONV_TAC WORD_BLAST);;

let EDWARDS25519_ENCODE_SUBROUTINE_CORRECT = time prove
 (`!z p x y pc returnaddress.
      nonoverlapping (word pc,0x108) (z,32)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) edwards25519_encode_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; p] s /\
                bignum_pair_from_memory(p,4) s = (x,y))
           (\s. read PC s = returnaddress /\
                (x < p_25519 /\ y < p_25519
                ==> read (memory :> bytelist(z,32)) s =
                    bytelist_of_num 32 (ed25519_encode (&x,&y))))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,32)])`,
  ARM_ADD_RETURN_NOSTACK_TAC EDWARDS25519_ENCODE_EXEC
    EDWARDS25519_ENCODE_CORRECT);;
