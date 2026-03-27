(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
          Prove the constant-time and memory-safety property.
******************************************************************************)

needs "arm/proofs/base.ml";;
needs "arm/proofs/consttime.ml";;

(* In s2n-bignum, each assembly function must be proven to be functionally
  correct, and its correctness specification is represented in the
  `<function name>_SUBROUTINE_CORRECT` theorem.
  In Arm, for any assembly function f, there must be a theorem of name
  '<f>_SUBROUTINE_CORRECT'. In x86, there must be four variants for each function
  by a cartesian product of (has IBT?, is Windows ABI?), with the names of
  `<f>{_NOIBT?}{_WINDOWS?}_SUBROUTINE_CORRECT`.

  Additionally, assembly functions in s2n-bignum may be proven to be
  'safe', and the safety properties are named as `*_SUBROUTINE_SAFE`.
  The safety theorem describes the following two properties:

  1. Constant-time property
    Some inputs of an assembly function may contain private (sensitive)
  information. We want execution time of an assembly function to be
  independent from the contents of private inputs.

  2. Memory safety
    Memory safety ensures that all memory accesses during execution happen
  within the permitted memory area. The existing functional correctness specs
  has the `MAYCHANGE` predicate describing which memory areas may have been
  updated, but it still cannot catch the following two corner cases:
    (1) An unpermitted area was read.
    (2) An unpermitted area was silently used as a scratchpad, and then
        recovered to the original value.

  To formally describe & prove these properties, s2n-bignum's formal semantics
  of assembly instructions have a small extension that does not appear in the
  actual architecture: the abstract microarchitectural events.
  For example, a 'ldr' instruction in Arm adds the 'EventLoad(addr,access_size)'
  event to the 'events' field of the program state which is a list of
  microarchitectural events.
  Similarly, a 'str' instruction in Arm will add 'EventStore(addr,access_size)'
  to the event trace. Note that 'EventStore' does not take the stored value as a
  parameter because the stored value won't affect the execution time of 'str'
  (unless Data Memory-dependent Prefetcher is enabled, but it is disabled by
  default when running crypto libs).
  The full definitions of event can be found from the `uarch_event` inductive
  data type in common/safety.ml .

  The spec of a safety property then uses the 'ensures' predicate to inspect
  whether the output events satisfy the two properties. It inspects whether
  (1) The generated events are only depending on the public information, and
  (2) All memory accesses happen within the permitted area,
*)

(* ------------------------------------------------------------------------- *)
(* Proving the safety property of a straight-line code.                      *)
(* ------------------------------------------------------------------------- *)

(* As a start, a simple function that does not have a branch will be chosen and
  verified. The tactics used in this example can be also applied to a function
  that has a loop with constant number of iterations.

  The bignum_mux_4 function in {arm,x86}/p256/bignum_mux_4.S is a simple
  function that receives two input buffers of 32 bytes x[32] and y[32] as well
  as a boolean flag p. If p is zero, x is copied to the output buffer z[32].
  Otherwise, y is copied to z.

  This function must have constant-time execution in the sense that the
  execution time must not depend on the flag p. Also, the function must be
  memory-safe by
  (1) only writing to z[0..31] and
  (2) reading from x[0..31], y[0..32] and possibly z[0..32].

  Let's write the safety spec of this function. As it was done for the
  original functional correctness proofs, the core part of the function without
  callee-save register spills and ret instruction will be veriifed, then
  the full subroutine safety.
  The original correctness theorem BIGNUM_MUX_4_CORRECT was as follows:

  `forall p z x y m n pc.
     nonoverlapping (word pc,0x48) (z,8 * 4) /\
     (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4)) /\
     (y = z \/ nonoverlapping (y,8 * 4) (z,8 * 4))
     ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mux_4_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [p; z; x; y] s /\
                bignum_from_memory (x,4) s = m /\
                bignum_from_memory (y,4) s = n)
           (\s. read PC s = word (pc + 0x44) /\
                bignum_from_memory (z,4) s =
                  if ~(p = word 0) then m else n)
          (MAYCHANGE [PC; X0; X4] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`

  The safety spec of bignum_mux_4 can be written as follows:
*)

needs "arm/proofs/bignum_mux_4.ml";;

let bignum_mux_4_safety_spec =
  `exists f_events.
      forall e p z x y pc.
        nonoverlapping (word pc,72) (z,8 * 4) /\
        (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4)) /\
        (y = z \/ nonoverlapping (y,8 * 4) (z,8 * 4))
        ==> ensures arm
            (\s.
                aligned_bytes_loaded s (word pc) bignum_mux_4_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [p; z; x; y] s /\
                read events s = e)
            (\s.
                read PC s = word (pc + 68) /\
                (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events x y z pc /\
                      memaccess_inbounds e2 [x,32; y,32; z,32] [z,32]))
            (MAYCHANGE [PC; X0; X4] ,,
             MAYCHANGE SOME_FLAGS ,,
             MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bignum (z,4)])`;;

(* There are a few interesting points in bignum_mux_4_safety_spec.

  1. The outermost existential quantifier, f_events, enforces that the
     new microarchitectural events only depend on public information.

    The spec says that there exists some function 'f_events' which returns
  a new list of microarchitectural events (e2) after running this program.
  The arguments to f_events are the buffer addresses (x, y, z) and the program
  counter (pc), which are all public information. Note that 'p' must not
  be listed as an argument because it is a private data.
    The benefit of existentially quantifying f_events is that it avoids writing
  the full list of events in the spec which will become too lengthy &
  unreadable. The existential quantification must be located outside the forall
  quantification, not inside, to make f_events independent from possibly
  private parameters like 'p' in forall.
    This style of constant-time property description is written in detail in
  CAV'25, "Relational Hoare Logic for Realistically Modelled Machine Code".
  A slight difference from the paper is that the paper used 'ensures_n' whereas
  the s2n-bignum mainstream uses 'ensures', to reuse existing tactics and lemmas
  at the expense of losing the equivalence property between 'ensures_n' and
  'ensures2'.

  2. The postcondition checks memory safety using the 'memaccess_inbounds'
     predicate.

    'memaccess_inbounds e2 [x,32; y,32; z,32] [z,32]' checks that the new event
  list e2 does not
    (1) have memory read events that don't fit in [x,32; y,32; z,32], and
    (2) have memory write events that don't fit in [z,32].

  3. The MAYCHANGE part is copied from the functional correctness.

    However, it is often beneficial to simply use '\s s'. true' because the
  MAYCHANGE part is already proven in the original functional correctness
  statement (BIGNUM_MUX_4_CORRECT). Using simple '\s s'. true' makes the tactics
  used while proving the safety spec faster.
    In this example, this was necessary because we are going to do compositional
  reasoning over the safety proof. Compositional reasoning is about reusing
  already proven facts about a smaller code snippet to prove a larger code.
  In this case, the MAYCHANGE part has to be concretely defined, like
  bignum_mux_4_safety_spec.
*)

(*
  For the simple straight-line code, PROVE_SAFETY_SPEC_TAC can be used. It does
  symbolic simulation from the beginning until the PC counter at postcondition
  is hit, accumulates the events, and checks whether the postcondition holds.
*)
let bignum_mux_4_safe = time prove
 (`exists f_events.
      forall e p z x y pc.
        nonoverlapping (word pc,72) (z,8 * 4) /\
        (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4)) /\
        (y = z \/ nonoverlapping (y,8 * 4) (z,8 * 4))
        ==> ensures arm
            (\s.
                aligned_bytes_loaded s (word pc) bignum_mux_4_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [p; z; x; y] s /\
                read events s = e)
            (\s.
                read PC s = word (pc + 68) /\
                (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events x y z pc /\
                      memaccess_inbounds e2 [x,32; y,32; z,32] [z,32]))
            (MAYCHANGE [PC; X0; X4] ,,
             MAYCHANGE SOME_FLAGS ,,
             MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bignum (z,4)])`,
  (* Assert that the goal is same as bignum_mux_4_safety_spec *)
  ASSERT_CONCL_TAC bignum_mux_4_safety_spec THEN
  (* Go! *)
  PROVE_SAFETY_SPEC_TAC BIGNUM_MUX_4_EXEC);;

(*
  Actually, the above spec is automatically generated from a helper function,
  mk_safety_spec. This is possible because tools/collect-signatures.py parses
  comments of as well as the C function declarations in s2n-bignum.h and
  automatically generates an OCaml list that contains a list of input/output
  buffers. It conservatively marks all function parameters other than buffer
  addresses and buffer sizes as private information.

  needs "arm/proofs/subroutine_signatures.ml";;

  let bignum_mux_4_safety_spec,public_vars = mk_safety_spec
      ~keep_maychanges:true
      (assoc "bignum_mux_4" subroutine_signatures)
      BIGNUM_MUX_4_CORRECT
      BIGNUM_MUX_4_EXEC;;

  public_vars can be passed to PROVE_SAFETY_SPEC_TAC as an optional argument for
  faster symbolic simulation. It will help the tactic ignore values of registers
  that are not described in public_vars.
*)

(* The next step is to prove the subroutine version of the safety spec using
  bignum_mux_4_safe.
  Again, mk_safety_spec can be used to autogenerate the below spec.

  let bignum_mux_4_subroutine_safety_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "bignum_mux_4" subroutine_signatures)
    BIGNUM_MUX_4_SUBROUTINE_CORRECT
    BIGNUM_MUX_4_EXEC;;
*)

let bignum_mux_4_subroutine_safe = time prove
 (`exists f_events.
       forall e p z x y pc returnaddress.
           nonoverlapping (word pc,72) (z,8 * 4) /\
           (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4)) /\
           (y = z \/ nonoverlapping (y,8 * 4) (z,8 * 4))
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc) bignum_mux_4_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [p; z; x; y] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events x y z pc returnaddress /\
                         memaccess_inbounds e2 [x,32; y,32; z,32] [z,32]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bignum (z,4)])`,
  (* Use ARM_ADD_RETURN_NOSTACK_TAC which already worked for proving subroutine
     spec in the functional correctness world. *)
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MUX_4_EXEC bignum_mux_4_safe THEN

  (* Leaves the following subgoal, which is derived from the 'exists e2. ...'
     clause in the postcondition:
      `exists e2.
        CONS (EventJump (word (pc + 68),returnaddress))
          (APPEND (f_events_callee1 x y z pc) (APPEND [] e)) =
          APPEND e2 e /\
        e2 = f_events x y z pc returnaddress /\
        memaccess_inbounds e2 [x,32; y,32; z,32] [z,32]`

    To prove this kind of goal, DISCHARGE_SAFETY_PROPERTY_TAC will almost always
    work.
  *)
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Proving safety of a program with conditional branches or unbounded loops. *)
(* ------------------------------------------------------------------------- *)

(* If the program of interest has a conditional branch or unbounded loop,
  the end-to-end symbolic simulation tactic (PROVE_SAFETY_SPEC_TAC) won't work.
  Instead, you can use CONCRETIZE_F_EVENTS_TAC which receives a scaffolding of
  the structure of f_events that will mimic the control flow structure of the
  program. After that, the ensures with scaffolding can be broken down
  into smaller ensure triples using tactics for Hoare logic rules
  (ENSURES_EVENTS_SEQUENCE_TAC and ENSURES_EVENTS_WHILE_UP2_TAC).

  The scaffolding of f_events typically follows the flow of the functional
  correctness proof. For example, if the functional correctness proof
  special-cases n = 0 and do symbolic simulation in this case, then the
  scaffolding will also have 'if n = 0 then ... else ...'.

  For its example, bignum_mod_n25519 will be illustrated. It takes a big integer
  x of k words (8*k bytes), and stores (n % n_25519) (where n_25519 is a large
  constant) to buffer z of 4 words. Proving its functional correctness needs
  expertise in the algorithmic details, but proving its safety does not need
  that much.
*)
let bignum_mod_n25519_mc =
  define_from_elf "bignum_mod_n25519_mc" "arm/curve25519/bignum_mod_n25519.o";;

let BIGNUM_MOD_N25519_EXEC = ARM_MK_EXEC_RULE bignum_mod_n25519_mc;;

let bignum_mod_n25519_safe = time prove
 (`exists f_events.
        forall e z k x pc.
            nonoverlapping (word pc,304) (z,32)
            ==> ensures arm
                (\s.
                     aligned_bytes_loaded s (word pc) bignum_mod_n25519_mc /\
                     read PC s = word pc /\
                     C_ARGUMENTS [z; k; x] s /\
                     read events s = e)
                (\s.
                     read PC s = word (pc + 248) /\
                     (exists e2.
                          read events s = APPEND e2 e /\
                          e2 = f_events x z k pc /\
                          memaccess_inbounds e2 [x,val k * 8; z,32] [z,32]))
                (\s s'. true)`,

  (* Give a scaffolding to f_events. Each f_ev* variable corresponds to
     a sequence of microarchitectural events that can be simply proven with
     end-to-end symbolic simluation tactic. *)
  CONCRETIZE_F_EVENTS_TAC
    `\(x:int64) (z:int64) (k:int64) (pc:num).
      // bignum_mod_n25519 has shortcuts when n < 4, and a special case when
      // n = 4. Typically corresponds to ASM_CASES_TAC or tactics like that.
      if val k = 0 then
        f_ev_k0 x z k pc
      else if val k = 1 then
        f_ev_k1 x z k pc
      else if val k = 2 then
        f_ev_k2 x z k pc
      else if val k = 3 then
        f_ev_k3 x z k pc
      else
        // This APPEND concatenates two event lists, each of which is created
        // after ENSURES_EVENTS_SEQUENCE_TAC .
        APPEND
          (if val k = 4 then
            f_ev_4 x z k pc
           else
            // This 'APPEND post (APPEND (ENUMERATEL <loopcount> body) pre)'
            // represents the list of events for three sub ensures,
            // created after ENSURES_EVENTS_WHILE_UP2_TAC .
            APPEND
              (f_ev_loop_post x z k pc)
              (APPEND
                (ENUMERATEL (val k - 4) (\i. f_ev_loop x z k pc i))
                (f_ev_loop_pre x z k pc)))
          (f_ev_1 x z k pc)
      :(uarch_event) list` THEN

  (* Instantiate existential variables 'f_ev*' as metavariables. *)
  (* META_EXISTS_TAC is a handy tactic for instantiating existentially
     quantified variable 'x' in the goal 'exists x. ..' where x is some var.
     Compared to `EXISTS_TAC` which has to immediately mention
     what `x` is, `META_EXISTS_TAC` defers the concrete value of `x` until
     special tactics 'UNIFY_REFL_TAC' and 'UNIFY_ACCEPT_TAC' eventually
     tell that 'x was supposed to be instantiated like this!'.
     This is extensively used in safety proofs to defer the instantiation of
     list of microarchitectural events, like 'f_events', because otherwise the
     HOL Light user has to give a lengthy expression for that which can be
     prone to errors.
  *)
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN

  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN

  ABBREV_TAC `k' = val (k:int64)` THEN
  SUBGOAL_THEN `k' < 2 EXP 64` ASSUME_TAC THENL [
    EXPAND_TAC "k'" THEN MATCH_ACCEPT_TAC VAL_BOUND_64; ALL_TAC
  ] THEN
  (* The four shortcuts. The lengthy expression 'e2 = ...' in postcondition
     is simplified. *)
  ASM_CASES_TAC `k' < 4` THENL [
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
      `k < 4 ==> k = 0 \/ k = 1 \/ k = 2 \/ k = 3`)) THEN
    STRIP_TAC THENL [
      ASM_REWRITE_TAC[ARITH] THEN
      ARM_SIM_TAC BIGNUM_MOD_N25519_EXEC (1--9) THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;

      (* k = 1 *)
      ASM_REWRITE_TAC[ARITH] THEN
      SUBST1_TAC (ISPEC `k:int64` (GSYM WORD_VAL)) THEN
      ARM_SIM_TAC BIGNUM_MOD_N25519_EXEC (1--12) THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;

      (* k = 2 *)
      ASM_REWRITE_TAC[ARITH] THEN
      SUBST1_TAC (ISPEC `k:int64` (GSYM WORD_VAL)) THEN
      ARM_SIM_TAC BIGNUM_MOD_N25519_EXEC (1--15) THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;

      (* k = 3 *)
      ASM_REWRITE_TAC[ARITH] THEN
      SUBST1_TAC (ISPEC `k:int64` (GSYM WORD_VAL)) THEN
      ARM_SIM_TAC BIGNUM_MOD_N25519_EXEC (1--17) THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
    ];

    ALL_TAC
  ] THEN

  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (ARITH_RULE
    `~(k < 4) ==> ~(k = 0) /\ ~(k = 1) /\ ~(k = 2) /\ ~(k = 3)`)) THEN
  ASM_REWRITE_TAC[] THEN

  (* Recognizes the outermost APPEND in the postcondition of the goal
     ensures and splits that & distribute each of them to two subgoals.
     The definition of ENSURES_EVENTS_SEQUENCE_TAC (common/consttime.ml)
     has detailed explanation.
  *)
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x88`
   `\s. read X0 s = z /\
        read X2 s = x /\
        read X1 s = word(k' - 4)` THEN CONJ_TAC THENL [
    ARM_SIM_TAC ~canonicalize_pc_diff:false
      BIGNUM_MOD_N25519_EXEC (1--34) THEN
    CONJ_TAC THENL [
      IMP_REWRITE_TAC[GSYM WORD_SUB2] THEN
      EXPAND_TAC "k'" THEN ASM_REWRITE_TAC[WORD_VAL] THEN ASM_ARITH_TAC;
      ALL_TAC
    ] THEN

    (* to help memory inbounds reasoning (got from fn correctness proof *)
    SUBGOAL_THEN
      `word_add (word_shl (word_sub k (word 4)) 3) x:int64 =
       word_add x (word (8 * (k' - 4)))` MP_TAC THENL [
      SUBST1_TAC (ISPEC `k:int64` (GSYM WORD_VAL)) THEN
      IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL [
        CONV_TAC WORD_RULE; SIMPLE_ARITH_TAC];
      ALL_TAC
    ] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    (* rewrite k with word k', because the LHS of 'APPEND e2 e' in the
       conclusion is using k' whereas the RHS of 'e2 = ...' in the conclusion
       is using k. *)
    SUBST1_TAC (ISPEC `k:int64` (GSYM WORD_VAL)) THEN
    REWRITE_TAC[ASSUME `val (k:int64) = k'`] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC
  ] THEN

  (*** Finish off the k = 4 case which is now just the writeback ***)

  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (ARITH_RULE
   `~(k' < 4) ==> k' = 4 \/ (~(k' = 4) /\ 4 < k')`))
  THENL
   [ASM_REWRITE_TAC[SUB_REFL;MULT_0] THEN
    ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC BIGNUM_MOD_N25519_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC] THEN

  ASM_REWRITE_TAC[] THEN
  (* The loop.
     The definition of ENSURES_EVENTS_WHILE_UP2_TAC (common/consttime.ml)
     has detailed explanation. *)
  ENSURES_EVENTS_WHILE_UP2_TAC `k' - 4` `pc + 0x8c` `pc + 0xf0`
   `\i s. read X0 s = z /\
          read X2 s = x /\
          read X1 s = word ((k' - 4) - i)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL [
    SIMPLE_ARITH_TAC;

    (* Begin to precondition *)
    ENSURES_INIT_TAC "s0" THEN
    (* Break 'exists e2. ...' in the precondition. *)
    STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC BIGNUM_MOD_N25519_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    (* Prove that the program counter is right *)
    CONJ_TAC THENL [
      IMP_REWRITE_TAC[VAL_WORD;DIMINDEX_64;MOD_LT] THEN
      SIMPLE_ARITH_TAC;

      ALL_TAC
    ] THEN
    (* Prove loop counter equality *)
    CONJ_TAC THENL [REWRITE_TAC[SUB_0]; ALL_TAC] THEN
    (* The main part, 'exists e2. ...'. *)
    (* rewrite k with word k' *)
    SUBST1_TAC (ISPEC `k:int64` (GSYM WORD_VAL)) THEN
    REWRITE_TAC[ASSUME `val (k:int64) = k'`] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (* Main loop *)
    ALL_TAC;

    (* Postcondition to end *)
    ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC BIGNUM_MOD_N25519_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC
  ] THEN

  (* The loop body *)
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC BIGNUM_MOD_N25519_EXEC (1--25) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* Prove that the program counter is right *)
  CONJ_TAC THENL [
    REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
    IMP_REWRITE_TAC[VAL_WORD;DIMINDEX_64;MOD_LT] THEN
    REPEAT CONJ_TAC THENL [
      GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN SIMPLE_ARITH_TAC;
      SIMPLE_ARITH_TAC;
      SIMPLE_ARITH_TAC;
    ];
    ALL_TAC
  ] THEN
  (* Prove loop counter equality *)
  CONJ_TAC THENL [
    IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
    [ AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC ];
    ALL_TAC
  ] THEN
  (* The main part, 'exists e2. ...'. *)
  (* rewrite k with word k' *)
  SUBST1_TAC (ISPEC `k:int64` (GSYM WORD_VAL)) THEN
  REWRITE_TAC[ASSUME `val (k:int64) = k'`] THEN
  (* safety_print_log := 1;; revealed that CONTAINED_TAC could not prove
     expressions including `word_sub (word (k' - 4 - i)) (word 1)`. *)
  SUBGOAL_THEN `word_sub (word (k' - 4 - i)) (word 1) =
                word (k' - 4 - (i + 1)):int64` SUBST_ALL_TAC THENL [
    IMP_REWRITE_TAC[WORD_SUB2] THEN
    CONJ_TAC THENL [ AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC];
    ALL_TAC
  ] THEN
  (* .. and manual inspection of sub-tactics reveal this *)
  MAP_EVERY VAL_INT64_TAC [`k':num`; `k'-4`] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;


(* ------------------------------------------------------------------------- *)
(* Reusing functional correctness tactics for proving the safety property    *)
(* ------------------------------------------------------------------------- *)

(* You can reuse the most of existing tactics for functional correctness. This
  includes

  - ENSURES_INIT_TAC, ENSURES_FINAL_STATE_TAC, {ARM,X86}_STEPS_TAC:
      can be used without any change

  - *_STACK_TAC/*_NOSTACK_TAC: does not immediately discharge the goal
      and will leave a subgoal 'exists e2. ...'.
      DISCHARGE_SAFETY_PROPERTY_TAC will always prove this.

  - {ARM,X86}_SIM_TAC: with two extra arguments, preprocess_tac and
      canonicalize_pc_diff. preprocess_tac must be set to
      'TRY STRIP_EXISTS_ASSUM_TAC', and canonicalize_pc_diff be set to 'false',
      like this:
        ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false MY_EXEC (..)

  - {ARM,X86}_SUBROUTINE_SIM_TAC: needs is_safety_thm to be set to true, and
      the 'subth' argument must have picked from the assumption registered
      by ASSUME_CALLEE_SAFETY_TAILED_TAC.
      As an example, let's assume that a function f_caller is calling f_callee,
      and f_callee has a safety property theorem named 'f_callee_safe'.
      You can do:

      (* the current goalstate is '|- exists f_events. forall e .... ' *)
      ASSUME_CALLEE_SAFETY_TAILED_TAC smaller_function_safe "H_MY_SAFE" THEN
      META_EXISTS_TAC THEN
      ... THEN
      REMOVE_THEN "H_MY_SAFE" (fun callee_safety_th ->
        X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
          (f_caller_mc,F_CALLER_EXEC,<offset>,F_CALLEE_EXEC,callee_safety_th)
          [`e:(uarch_event)list`; ..(arguments to f_callee)..] <step number>
        THENL [
          ALL_TAC;
          LABEL_TAC "H_MY_SAFE" callee_safety_th (* Register H_MY_SAFE again *)
        ]);;

      Note that {X86,ARM}_SUBROUTINE_SIM_TAC is now returning two subgoals.
      The first subgoal can be proven with EXISTS_E2_TAC.
*)


(* ------------------------------------------------------------------------- *)
(* How can we only prove memory safety but not constant-time property?       *)
(* ------------------------------------------------------------------------- *)

(* You can prove the memory safety property of a program, but not constant-time
  property as follows:

  1. The spec won't need to quantify f_events! The goal is just traditional
     ensures.
  2. You can put this at the postcondition:
    `exists e2.
      read events s = APPEND e2 e /\ memaccess_inbounds e2 [..] [..]`
  3. Just do the symbolic simulation, then reuse DISCHARGE_SAFETY_PROPERTY_TAC.
    It can handle the variant of postcondition having no f_events.

  For slightly more advanced programs like bignum_mod_n25519, using the
  traditional ENSURES_*_TAC with invariants containing
  `read events s = APPEND e2 e /\ memaccess_inbounds e2 [..] [..]` will work.
*)

let bignum_mux_4_memory_safe = time prove
 (`forall e p z x y pc.
      nonoverlapping (word pc,72) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4)) /\
      (y = z \/ nonoverlapping (y,8 * 4) (z,8 * 4))
      ==> ensures arm
          (\s.
              aligned_bytes_loaded s (word pc) bignum_mux_4_mc /\
              read PC s = word pc /\
              C_ARGUMENTS [p; z; x; y] s /\
              read events s = e)
          (\s.
              read PC s = word (pc + 68) /\
              (exists e2.
                    read events s = APPEND e2 e /\
                    memaccess_inbounds e2 [x,32; y,32; z,32] [z,32]))
          (MAYCHANGE [PC; X0; X4] ,,
            MAYCHANGE SOME_FLAGS ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bignum (z,4)])`,
  (* Start with the traditional proof style. *)
  REPEAT GEN_TAC THEN DISCH_THEN ((MAP_EVERY ASSUME_TAC) o CONJUNCTS) THEN
  REWRITE_TAC[C_ARGUMENTS;SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC BIGNUM_MUX_4_EXEC (1--17) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN

  (* Now the `exists e2. ....` part. *)
  DISCHARGE_SAFETY_PROPERTY_TAC);;