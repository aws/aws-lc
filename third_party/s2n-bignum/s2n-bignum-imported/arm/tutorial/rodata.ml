(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
          Verifying a program that reads constant data from .rodata
******************************************************************************)

needs "arm/proofs/base.ml";;

(* The following command will print the assertion checker fn of
   "arm/tutorial/rodata.o":

   print_literal_relocs_from_elf "arm/tutorial/rodata.o";;

   Or, you can also use

   save_literal_relocs_from_elf "out.txt" "arm/tutorial/rodata.o";;
*)

let a_mc,a_constants_data = define_assert_relocs_from_elf "a_mc"
    "arm/tutorial/rodata.o"
(fun w BL ADR ADRP ADD_rri64 -> [
(* int f(int) *)
  w 0xaa0003e3;         (* arm_MOV X3 X0 *)

  (* NOTE: The two entries below have the names of symbols. If they appear as
     an empty string on your custom object file, please check whether the
     symbols are defined as global in assembly. Local symbols will not have
     their names recorded in string table. *)
  ADRP (mk_var("x",`:num`),0,4,10);
  ADD_rri64 (mk_var("x",`:num`),0,10,10);

  w 0xaa0303e1;         (* arm_MOV X1 X3 *)
  w 0xb8617941;         (* arm_LDR W1 X10 (Shiftreg_Offset X1 2) *)

  ADRP (mk_var("y",`:num`),0,20,11);
  ADD_rri64 (mk_var("y",`:num`),0,11,11);

  w 0xaa0303e2;         (* arm_MOV X2 X3 *)
  w 0xb8627960;         (* arm_LDR W0 X11 (Shiftreg_Offset X2 2) *)
  w 0x0b000020;         (* arm_ADD W0 W1 W0 *)
  w 0xd65f03c0;         (* arm_RET X30 *)

(* int g(int) *)
  ADRP (mk_var("z",`:num`),0,44,10);
  ADD_rri64 (mk_var("z",`:num`),0,10,10);
  w 0xb9400141;         (* arm_LDR W1 X10 (Immediate_Offset (word 0)) *)
  w 0x8b000020;         (* arm_ADD X0 X1 X0 *)
  w 0x17fffff1          (* arm_B (word 268435396) *)
]);;

(* Compared to the result of define_asserts_from_elf, the return value of
    define_assert_relocs_from_elf has the following differences:

    1. It returns a_constants_data, which is a list of thm.
      Each thm describes a definition of an object in a read-only section:

      # a_constants_data;;

      - : thm list =
      [|- z_data = [word 30; word 0; word 0; word 0];
       |- y_data = [word 1; word 0; word 0; word 0; ...];
       |- x_data = [word 2; word 0; word 0; word 0; ...]]

    2. The returned a_mc is a function that takes the addresses of pc, x, y and
       (x and y are the addresses of the two constant arrays) and returns
       the corresponding machine code.

      # a_mc;;

      - : thm =
      |- forall x pc y. a_mc pc x y = CONS (word 227) (...)
*)

let EXEC = ARM_MK_EXEC_RULE a_mc;;

(* Two helper tactics.
   1. INTRO_READ_MEMORY_FROM_BYTES8_TAC t:
      If t is `read (memory :> bytesN ...) sM`, prove a theorem
      `read (memory :> bytesN ...) sM = <some expr>` and introduce it
      as an assumption, from the existing `read (memory :> bytes8 ..) sM = ..`
      assumptions.

   2. EXPLODE_BYTELIST_ASSUM_TAC:
      Find assumption `read (memory :> bytelist (...)) s = ..` and explode
      it to a list of `read (memory :> bytes8 (...)) s = ..` and reintroduce
      them as assumptions.
*)
let INTRO_READ_MEMORY_FROM_BYTES8_TAC (t:term) =
  (* Convert t into word_joins of 1-byte reads. *)
  let r = REWRITE_CONV [READ_MEMORY_BYTESIZED_SPLIT] t in
  (* Offset canonicalization, and then rewrite using assumptions *)
  let r = REWRITE_RULE[WORD_ADD_ASSOC_CONSTS;WORD_ADD_0;ARITH] r in
  MP_TAC r THEN
  ASM (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)) [] THEN
  CONV_TAC (LAND_CONV WORD_REDUCE_CONV) THEN
  DISCH_TAC;;

let EXPLODE_BYTELIST_ASSUM_TAC =
  FIRST_X_ASSUM (fun th ->
    let _ = find_term (fun t -> name_of t = "bytelist") (concl th) in
    (* Unfold the constant arrays! *)
    let unfolded_bytes_loaded = REWRITE_RULE a_constants_data th in
    (* Fold LENGTH array, and explode arr using BYTELIST_EXPAND_CONV *)
    MP_TAC (CONV_RULE (ONCE_DEPTH_CONV LENGTH_CONV THENC
                      LAND_CONV BYTELIST_EXPAND_CONV)
            unfolded_bytes_loaded)) THEN
  (* [a;b;..] = [x;y;..] is a = x /\ b = y /\ ... *)
  REWRITE_TAC [CONS_11] THEN
  STRIP_TAC;;


let F_SPEC = prove(`forall x y z i pc retpc.
  // These two assumptions state that the distance between symbol x and pc+4
  // (which is the first adrp) do not overflow, and so does symbol y and
  // pc+20.
  adrp_within_bounds (word x) (word (pc + 4)) /\
  adrp_within_bounds (word y) (word (pc + 20)) /\
  val i < 10
  ==>
  ensures arm
    (\s. aligned_bytes_loaded s (word pc) (a_mc pc x y z) /\
         read (memory :> bytelist (word x, LENGTH x_data)) s = x_data /\
         read (memory :> bytelist (word y, LENGTH y_data)) s = y_data /\
         read PC s = word pc /\
         read X0 s = i /\
         read X30 s = retpc)
    (\s. read W0 s = word (3 * (1 + val i)) /\
         read PC s = retpc)
    (MAYCHANGE [X0; X1; X2; X3; X10; X11; PC] ,, MAYCHANGE [events])`,

  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (* Let's prove the constant array is storing some structured int sequence. *)
  SUBGOAL_THEN
      `read (memory :> bytes32 (word_add (word x) (word (4 * val (i:int64))))) s0 = word (2 * (val i+1)) /\
       read (memory :> bytes32 (word_add (word y) (word (4 * val i)))) s0 = word (val i+1)`
      MP_TAC THENL [

    (* Explode the 40-byte constant memory reads into 40 1-bytes!
       Do it twice, one for x and one for y. *)
    REPEAT_N 2 EXPLODE_BYTELIST_ASSUM_TAC THEN

    (* For each case where i < 10, concretely evaluate the values from the
       exploded bytes, proving the equality. *)
    ABBREV_TAC `i' = val (i:int64)` THEN
    UNDISCH_TAC `i' < 10` THEN
    SPEC_TAC (`i':num`,`i':num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[ARITH;WORD_ADD_0] THEN

    REPEAT CONJ_TAC THEN (fun (asl,w) ->
      INTRO_READ_MEMORY_FROM_BYTES8_TAC (lhs w) (asl,w)
    ) THEN ASM_REWRITE_TAC[];

    ALL_TAC
  ] THEN

  STRIP_TAC THEN

  ARM_STEPS_TAC EXEC (1--3) THEN
  FIRST_X_ASSUM (fun th -> MP_TAC th THEN IMP_REWRITE_TAC[ADRP_ADD_FOLD] THEN DISCH_TAC) THEN

  ARM_STEPS_TAC EXEC (4--7) THEN
  FIRST_X_ASSUM (fun th -> MP_TAC th THEN IMP_REWRITE_TAC[ADRP_ADD_FOLD] THEN DISCH_TAC) THEN

  ARM_STEPS_TAC EXEC (8--11) THEN

  (* Prove the postcondition. *)
  ENSURES_FINAL_STATE_TAC THEN

  ASM_REWRITE_TAC[WREG_EXPAND_CLAUSES;READ_ZEROTOP_32] THEN
  REWRITE_TAC[WORD_BLAST`word_zx (word_zx (x:(32)word):(64)word):(32)word = x`] THEN
  CONV_TAC WORD_RULE);;


(* Proving the specification of function g(i) that calls f(i + z). *)

let G_SPEC = prove(`forall x y z i pc retpc.
  adrp_within_bounds (word x) (word (pc + 4)) /\
  adrp_within_bounds (word y) (word (pc + 20)) /\
  adrp_within_bounds (word z) (word (pc + 44)) /\
  val i < 9
  ==>
  ensures arm
    (\s. aligned_bytes_loaded s (word pc) (a_mc pc x y z) /\
         read (memory :> bytelist (word x, LENGTH x_data)) s = x_data /\
         read (memory :> bytelist (word y, LENGTH y_data)) s = y_data /\
         read (memory :> bytelist (word z, LENGTH z_data)) s = z_data /\
         read PC s = word (pc + 0x2c) /\
         read X0 s = i /\
         read X30 s = retpc)
    (\s. read W0 s = word (3 * (2 + val i)) /\
         read PC s = retpc)
    (MAYCHANGE [X0; X1; X2; X3; X10; X11; PC] ,, MAYCHANGE [events])`,

  REPEAT STRIP_TAC THEN

  ENSURES_INIT_TAC "s0" THEN

  ARM_STEPS_TAC EXEC (1--2) THEN
  FIRST_X_ASSUM (fun th -> MP_TAC th THEN IMP_REWRITE_TAC[ADRP_ADD_FOLD] THEN DISCH_TAC) THEN

  (* Prepare load z. *)
  EXPLODE_BYTELIST_ASSUM_TAC THEN
  INTRO_READ_MEMORY_FROM_BYTES8_TAC
    `read (memory :> bytes32 (word z)) s2` THEN
  (* Expand read W0 to read X0. *)
  RULE_ASSUM_TAC(REWRITE_RULE[WREG_EXPAND_CLAUSES;READ_ZEROTOP_32]) THEN
  ARM_STEPS_TAC EXEC (3--4) THEN

  SUBGOAL_THEN `val (word_add (word 1) i:int64) < 10` ASSUME_TAC THENL [
    REWRITE_TAC[VAL_WORD_ADD;VAL_WORD;DIMINDEX_64] THEN ASM_ARITH_TAC;
    ALL_TAC
  ] THEN
  ARM_STEPS_TAC EXEC [5] THEN

  (* Call ARM_SUBROUTINE_SIM_TAC with its arguments. *)
  ARM_SUBROUTINE_SIM_TAC
   (SPEC_ALL a_mc,EXEC,0,SPEC_ALL a_mc,F_SPEC)
   [`x:num`;`y:num`;`z:num`;`read X0 s`;
    `pc:num`; `read X30 s`] 6 THEN

  (* Prove the postcondition. *)
  ENSURES_FINAL_STATE_TAC THEN

  ASM_REWRITE_TAC[VAL_WORD_ADD;DIMINDEX_64] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_REDUCE_CONV THEN
  IMP_REWRITE_TAC[MOD_LT] THEN ASM_ARITH_TAC);;
