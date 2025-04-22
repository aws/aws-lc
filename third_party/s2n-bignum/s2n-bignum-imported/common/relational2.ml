(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(*         Relational Hoare Logic for proving program relation.              *)
(* ========================================================================= *)

(**** Proofs in this file can be easily converted to the e-g form.
      Please use this directive in REPL:
  unset_then_multiple_subgoals;;
 ****)

needs "common/relational_n.ml";;

(* ------------------------------------------------------------------------- *)
(* A relational hoare triple 'ensures2'. It is defined using 'eventually_n'. *)
(* ------------------------------------------------------------------------- *)

(* Define relational hoare triples using eventually_n. *)
let ensures2 = new_definition
  `ensures2 (step:S->S->bool) (precond:S#S->bool) (postcond:S#S->bool) (frame:S#S->S#S->bool)
            (step_calc1:S->num) (step_calc2:S->num) <=>
  !(s1_init:S) (s2_init:S). precond (s1_init,s2_init)
      ==> eventually_n step (step_calc1 s1_init)
            (\s1'. eventually_n step (step_calc2 s2_init)
                (\s2'. postcond (s1',s2') /\ frame (s1_init,s2_init) (s1',s2')) s2_init) s1_init`;;


(******************************************************************************
  We will describe why this definition was chosen by explaining problems of
  its alternative definitions.
  First, a natural definition of 'ensures' using a product of steps like below
  is problematic:

    'eventually
      (\(s1,s2) (s1',s2'). (step s1 s1' /\ s2 = s2') \/ (step s2 s2' /\ s1 = s1')
      P (sinit1,sinit2)'

  Let's assume that the post-condition P must hold at (s1,s2) = (0,1).
  Beginning from (0,0), if 'eventually' takes a step at s1 first:
    (0,0) -> (1,0)
  It cannot eventually reach at (0,1) because fst of (1,0) is already 1.
  EVENTUALLY_PROD_OF_STEPS_BAD proves that with this definition we
  cannot reach to a state (s1,s2) = (0,1) even if we increment step by step
    from (s1,s2) = (0,0)!
  Note that bounding the number of steps that 'eventually' can take cannot be
  a solution, because for this example 2 steps is enough to make it false.
 *****************************************************************************)

let EVENTUALLY_PROD_OF_STEPS_BAD =
  let lemma = prove(
  `!s. (0 < FST s /\ SND s = 0) ==>
    ~eventually
      (\(s:num#num) (s':num#num).
        (1 + FST s = FST s' /\ SND s = SND s') \/ (1 + SND s = SND s' /\ FST s = FST s'))
      (\(s:num#num). FST s = 0 /\ SND s = 1)
      s`,
  ONCE_REWRITE_TAC[TAUT`(P==>(~Q)) <=> (Q==>(~P))`] THEN
  MATCH_MP_TAC eventually_INDUCT THEN
  CONJ_TAC THENL [
    BETA_TAC THEN ARITH_TAC;

    ONCE_REWRITE_TAC[TAUT`(P==>(~Q)) <=> (Q==>(~P))`] THEN
    REWRITE_TAC[TAUT`~(P/\Q)<=>((~P)\/(~Q))`] THEN
    REPEAT STRIP_TAC THEN DISJ2_TAC THEN
    REWRITE_TAC[NOT_FORALL_THM;NOT_IMP;TAUT`~((~P)\/(~Q))<=>(P/\Q)`] THEN
    EXISTS_TAC `(1+FST (s:num#num),SND s)` THEN
    ASM_SIMP_TAC[] THEN ARITH_TAC
  ]) in
  prove(`~eventually
      (\(s:num#num) (s':num#num).
        (1 + FST s = FST s' /\ SND s = SND s') \/ (1 + SND s = SND s' /\ FST s = FST s'))
      (\(s:num#num). FST s = 0 /\ SND s = 1)
      (0,0)`,
    ONCE_REWRITE_TAC[eventually_CASES] THEN
    REWRITE_TAC[FST;SND;TAUT`~(P\/Q)<=>((~P)/\(~Q))`;ARITH_RULE`~(0=1)`;
      TAUT `~(P/\Q)<=>((~P)\/(~Q))`] THEN
    DISJ2_TAC THEN
    REWRITE_TAC[GSYM EXISTS_NOT_THM; NOT_IMP] THEN
    EXISTS_TAC `(1,0)` THEN
    REWRITE_TAC[FST;SND;ARITH_RULE`1+0=1`] THEN
    MATCH_MP_TAC lemma THEN SIMP_TAC[] THEN ARITH_TAC);;

(******************************************************************************
  Another candidate for ensures2 is defining it as a nested eventually:
      '!s1 s2. pre(s1,s2) ==>
        eventually (\s1'. eventually (\s2'. post(s1',s2')) s2) s1'

  However, this definition is also problematic because it cannot prove two
  natural properties of relational Hoare logic.

  1. It is not commutative (EVENTUALLY_NESTED_DOES_NOT_COMMUTE).
    Two 'eventually's cannot be swapped, meaning that we cannot prove this
  natural property:
        {  \s s'. pre s s'   }            {  \s s'. pre s' s   }
            prog1   prog2         <=/=>        prog2   prog1
        {  \s s'. post s s'  }            {  \s s'. post s' s  }

  This can be deduced from this fact:
      eventually step (\s'. eventually (\s''. P s' s'') sb) sa
      != eventually step (\s''. eventually (\s'. P s' s'') sa) sb --- (1)

  Let's assume that
  - sa is nondeterministically stepped to sa1 or sa2
  - sb is stepped to sb'
  - P s s' := (s = sa1 /\ s' = sb') \/ (s = sa2 /\ s' = sb)
  The LHS of the inequality (1) is true because
    (A) if s' is sa1, `eventually (\s''. P sa1 s'') sb` is true at s'' = sb'
    (B) if s' is sa2, `eventually (\s''. P sa2 s'') sb` is true at s'' = sb
  However, the RHS of (1) is false because
    (A) If s'' is sb, `eventually (\s'. P s' sb) sa` is false when sa -> sa1
    (B) If s'' is sb', `eventually (\s'. P s' sb') sa` is false when sa -> sa2

  2. It is not compositional (EVENTUALLY_NESTED_DOES_NOT_COMPOSE).
    We cannot prove this:
        { \s s'. P s s' }     { \s s'. Q s s' }        { \s s'. P s' s  }
             c1    c2     /\     c1'    c2'      =/=>    c1;c1'   c2;c2'
        { \s s'. Q s s' }     { \s s'. R s s' }        { \s s'. R s' s  }

  To prove this, we can use
  - step is defined as the one of commutativity case above
  - P s s' := s = sa /\ s' = sb
  - Q s s' := (s = sa1 \/ s = sa2) /\ s' = sb
  - R s s' := (s = sa1 /\ s' = sb) \/ (s = sa2 /\ s' = sb')
******************************************************************************)
let EVENTUALLY_NESTED_DOES_NOT_COMMUTE =
  let EVENTUALLY_STOP_TAC = ONCE_REWRITE_TAC[eventually_CASES] THEN BETA_TAC THEN DISJ1_TAC in
  let EVENTUALLY_NEXT_TAC = ONCE_REWRITE_TAC[eventually_CASES] THEN BETA_TAC THEN DISJ2_TAC in
  prove(
    `!(sa:S) (sb:S) (sa1:S) (sa2:S) (sb':S).
        ~(sa = sb) /\ ~(sa = sa1) /\ ~(sa = sa2) /\ ~(sb = sb') /\
        ~(sa1 = sa2) /\ ~(sa1 = sb) /\ ~(sa2 = sb) /\ ~(sb' = sa)
      ==> ?(step:S->S->bool) (P:S->S->bool).
        eventually step (\s'. eventually step (\s''. P s' s'') sb) sa /\
        ~ eventually step (\s''. eventually step (\s'. P s' s'') sa) sb`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* give step *)
  EXISTS_TAC `\(s:S) (s':S).
      (s = sa /\ (s' = sa1 \/ s' = sa2)) \/
      (s = sb /\ s' = sb')` THEN
  (* give P *)
  EXISTS_TAC `\(s:S) (s':S). (s = sa2 /\ s' = sb) \/ (s = sa1 /\ s' = sb')` THEN
  CONJ_TAC THENL [
    (* sa -> sa1|sa2 *)
    EVENTUALLY_NEXT_TAC THEN
    CONJ_TAC THENL [METIS_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THENL [
      (* sa -> sa1 *)
      SUBST_ALL_TAC (ASSUME `s':S=sa1`) THEN EVENTUALLY_STOP_TAC THEN
      (* sb -> sb' *)
      EVENTUALLY_NEXT_TAC THEN CONJ_TAC THENL [METIS_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      EVENTUALLY_STOP_TAC THEN METIS_TAC[];

      (* sa -> sa2 *)
      SUBST_ALL_TAC (ASSUME `s':S=sa2`) THEN EVENTUALLY_STOP_TAC THEN
      EVENTUALLY_STOP_TAC THEN METIS_TAC[];
    ];

    (* Now prove the ~eventually ... part. *)
    (* sb -> sb' or stop at sb *)
    ONCE_REWRITE_TAC[eventually_CASES] THEN BETA_TAC THEN
    ASM_REWRITE_TAC[] THEN
    STRIP_TAC THENL [
      (* stopped at sb. *)
      RULE_ASSUM_TAC (ONCE_REWRITE_RULE[eventually_CASES]) THEN
      FIRST_X_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[TAUT `(~(P/\Q)) <=> (~P \/ ~Q)`] THEN DISJ2_TAC THEN
      REWRITE_TAC[NOT_FORALL_THM;NOT_IMP] THEN
      EXISTS_TAC `sa1:S` THEN REWRITE_TAC[] THEN
      (* sa1 doesn't work *)
      ONCE_REWRITE_TAC[eventually_CASES] THEN ASM_REWRITE_TAC[];

      (* sb -> sb' *)
      FIRST_X_ASSUM (fun th -> MP_TAC (SPEC `s':S` th)) THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[eventually_CASES] THEN
      ASM_REWRITE_TAC[TAUT `(~(P \/ Q)) <=> (~P /\ ~Q)`] THEN
      (* ~eventually (\s. s = sa1) sa *)
      ONCE_REWRITE_TAC[eventually_CASES] THEN
      ASM_REWRITE_TAC[TAUT `(~(P/\Q)) <=> (~P \/ ~Q)`] THEN
      DISJ2_TAC THEN REWRITE_TAC[NOT_FORALL_THM;NOT_IMP] THEN
      EXISTS_TAC `sa2:S` THEN REWRITE_TAC[] THEN ONCE_REWRITE_TAC[eventually_CASES]
      THEN ASM_REWRITE_TAC[]
    ]
  ]);;

let EVENTUALLY_NESTED_DOES_NOT_COMPOSE =
  let EVENTUALLY_STOP_TAC = ONCE_REWRITE_TAC[eventually_CASES] THEN BETA_TAC THEN DISJ1_TAC in
  let EVENTUALLY_NEXT_TAC = ONCE_REWRITE_TAC[eventually_CASES] THEN BETA_TAC THEN DISJ2_TAC in
  let ASM_SIMPLIFY_ALL_TAC = ASM_REWRITE_TAC[
    TAUT`~(P\/Q)<=>((~P)/\(~Q))`;TAUT`~(P/\Q)<=>((~P)\/(~Q))`;NOT_IMP;NOT_FORALL_THM] in
  prove(
    `!(sa:S) (sb:S) (sa1:S) (sa2:S) (sb':S).
        ~(sa = sb) /\ ~(sa = sa1) /\ ~(sa = sa2) /\ ~(sb = sb') /\
        ~(sa1 = sa2) /\ ~(sa1 = sb) /\ ~(sa2 = sb) /\ ~(sb' = sa)
      ==> ?(step:S->S->bool) (P:S->S->bool) (Q:S->S->bool) (R:S->S->bool) .
        ~((!sa0 sb0. P sa0 sb0 ==> eventually step (\s''. eventually step (\s'. Q s' s'') sa0) sb0) /\
          (!sa1 sb1. Q sa1 sb1 ==> eventually step (\s''. eventually step (\s'. R s' s'') sa1) sb1)
          ==> (!sa0 sb0. P sa0 sb0 ==> eventually step (\s''. eventually step (\s'. R s' s'') sa0) sb0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* give step *)
  EXISTS_TAC `\(s:S) (s':S).
      (s = sa /\ (s' = sa1 \/ s' = sa2)) \/
      (s = sb /\ s' = sb')` THEN
  (* give P, Q and R *)
  EXISTS_TAC `\(s:S) (s':S). s = sa /\ s' = sb` THEN
  EXISTS_TAC `\(s:S) (s':S). (s = sa1 \/ s = sa2) /\ s' = sb` THEN
  EXISTS_TAC `\(s:S) (s':S). (s = sa1 /\ s' = sb) \/ (s = sa2 /\ s' = sb')` THEN
  REWRITE_TAC[NOT_IMP;NOT_FORALL_THM] THEN
  REPEAT CONJ_TAC THENL [
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    (* sb *) EVENTUALLY_STOP_TAC THEN
    (* sa->sa1|sa2 *) EVENTUALLY_NEXT_TAC THEN
    CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THENL (replicate (ASM_REWRITE_TAC[] THEN EVENTUALLY_STOP_TAC THEN ASM_REWRITE_TAC[]) 2);

    REPEAT STRIP_TAC THENL [
      ASM_REWRITE_TAC[] THEN EVENTUALLY_STOP_TAC THEN EVENTUALLY_STOP_TAC THEN ASM_REWRITE_TAC[];

      ASM_REWRITE_TAC[] THEN EVENTUALLY_NEXT_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN EVENTUALLY_STOP_TAC THEN EVENTUALLY_STOP_TAC THEN ASM_REWRITE_TAC[]
    ];

    MAP_EVERY EXISTS_TAC [`sa:S`;`sb:S`] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[eventually_CASES] THEN ASM_SIMPLIFY_ALL_TAC THEN CONJ_TAC THENL [
      (* sb stop *)
      (* sa next *)
      ONCE_REWRITE_TAC[eventually_CASES] THEN ASM_SIMPLIFY_ALL_TAC THEN
      DISJ2_TAC THEN EXISTS_TAC `sa2:S` THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[eventually_CASES] THEN ASM_SIMPLIFY_ALL_TAC;

      (* sb -> sb' *)
      DISJ2_TAC THEN EXISTS_TAC `sb':S` THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[eventually_CASES] THEN ASM_SIMPLIFY_ALL_TAC THEN
      ONCE_REWRITE_TAC[eventually_CASES] THEN ASM_SIMPLIFY_ALL_TAC THEN
      DISJ2_TAC THEN EXISTS_TAC `sa1:S` THEN ONCE_REWRITE_TAC[eventually_CASES] THEN
      ASM_SIMPLIFY_ALL_TAC
    ]
  ]);;

(* ------------------------------------------------------------------------- *)
(* Properties of two eventually_ns.                                          *)
(* ------------------------------------------------------------------------- *)

let EVENTUALLY_N_SWAP = prove(
  `!(step:S->S->bool) s1 s2 n m (P:S->S->bool).
   eventually_n step n (\s1'. eventually_n step m (\s2'. P s1' s2') s2) s1 ==>
   eventually_n step m (\s2'. eventually_n step n (\s1'. P s1' s2') s1) s2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eventually_n] THEN REPEAT STRIP_TAC THENL
  replicate (ASM_MESON_TAC[STEPS_NOSTUCK]) 3);;

let EVENTUALLY_N_NESTED_COMPOSE =
  prove(
    `!(step:S->S->bool) (P:S->S->bool) (Q:S->S->bool) (R:S->S->bool) n1 m1 n2 m2 sa0 sb0.
        eventually_n step n1 (\s''. eventually_n step m1 (\s'. Q s' s'') sa0) sb0 /\
        (!sa1 sb1. Q  sa1 sb1 ==>
                   eventually_n step n2 (\s''. eventually_n step m2 (\s'. R s' s'') sa1) sb1)
          ==> eventually_n step (n1+n2) (\s''. eventually_n step (m1+m2) (\s'. R s' s'') sa0) sb0`,
  REWRITE_TAC[eventually_n;STEPS_ADD] THEN REPEAT STRIP_TAC THENL [
    ASM_MESON_TAC[];

    ASM_CASES_TAC `n' < m1` THENL [
      ASM_MESON_TAC[];

      SUBGOAL_THEN `n' = m1 + (n' - m1)` SUBST_ALL_TAC THENL [
        ASM_ARITH_TAC; ALL_TAC
      ] THEN
      UNDISCH_TAC `steps (step:S->S->bool) (m1 + n' - m1) sa0 s'''` THEN
      GEN_REWRITE_TAC LAND_CONV [STEPS_ADD] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `n' - m1 < m2` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_MESON_TAC[]
    ];

    ASM_CASES_TAC `n' < n1` THENL [
      ASM_MESON_TAC[];

      SUBGOAL_THEN `n' = n1 + (n' - n1)` SUBST_ALL_TAC THENL [
        ASM_ARITH_TAC; ALL_TAC
      ] THEN
      SUBGOAL_THEN `n' - n1 < n2` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `steps (step:S->S->bool) (n1 + n' - n1) sb0 s'` THEN
      GEN_REWRITE_TAC LAND_CONV [STEPS_ADD] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM (fun th1 ->
        MP_TAC (MATCH_MP th1 (ASSUME `steps (step:S->S->bool) n1 sb0 s''`))) THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM (fun th -> MP_TAC (MATCH_MP STEPS_NOSTUCK th)) THEN
      STRIP_TAC THEN
      ASM_MESON_TAC[]
    ]
  ]);;


(******************************************************************************
  This shows that using nested eventually_n is equivalent to defining a
  product of steps and using with explicitly giving the number of steps to
  take on each program.
******************************************************************************)

let NESTED_EVENTUALLY_N_IS_PROD_OF_STEPS = prove(
  `!n1 n2 (s1:S) (s2:S) (step:S->S->bool) P.
    eventually_n step n1 (\s1'. eventually_n step n2 (\s2'. P s1' s2') s2) s1
    <=>
    ((!s1' s2'. steps step n1 s1 s1' /\ steps step n2 s2 s2' ==> P s1' s2') /\
    // There isn't a 'stuck' state at the end of a trace shorter than n
    (!s1' n1'. (n1' < n1 /\ steps step n1' s1 s1') ==> ?s1''. step s1' s1'') /\
    (!s2' n2'. (n2' < n2 /\ steps step n2' s2 s2') ==> ?s2''. step s2' s2''))`,

  REPEAT GEN_TAC THEN
  EQ_TAC THENL [
    DISCH_THEN (fun th ->
      MP_TAC (CONJ th (MATCH_MP EVENTUALLY_N_SWAP th))) THEN
    REWRITE_TAC [eventually_n] THEN STRIP_TAC THEN
    ASM_MESON_TAC[];

    REWRITE_TAC[eventually_n] THEN MESON_TAC[]
  ]);;

(* ------------------------------------------------------------------------- *)
(* Properties of ensures2.                                                   *)
(* ------------------------------------------------------------------------- *)

(* From ensures2 and proper implications one can prove some ensures. *)
let ENSURES2_ENSURES_N = prove(
  `!(step:S->S->bool) P Q C P2 Q2 C2 f_n1 f_n2.
      ensures2 step P Q C f_n1 f_n2 /\
      (!s2. P2 s2 ==> ?s1. P (s1,s2)) /\
      (!s1 s2. Q (s1,s2) ==> Q2 s2) /\
      (?C1. !s1 s2 s1' s2'. C (s1,s1') (s2,s2') <=> C1 s1 s2 /\ C2 s1' s2')
        ==> ensures_n step P2 Q2 C2 f_n2`,
  REWRITE_TAC [ensures_n;ensures2] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (fun th -> MP_TAC (MATCH_MP th (ASSUME `(P2:S->bool) s`)) THEN STRIP_TAC) THEN
  FIRST_X_ASSUM (fun th -> MP_TAC (MATCH_MP th (ASSUME `(P:(S#S->bool)) (s1,s)`)) THEN STRIP_TAC) THEN
  FIRST_X_ASSUM MP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [eventually_n] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM (fun th -> MP_TAC (MATCH_MP STEPS_NOSTUCK th) THEN STRIP_TAC) THEN
  FIRST_X_ASSUM (fun th -> MP_TAC (MATCH_MP th (ASSUME `steps (step:S->S->bool) (f_n1 s1) s1 s'`))) THEN
  BETA_TAC THEN
  ASM_MESON_TAC[EVENTUALLY_N_MONO]);;

(* We can combine two independent ensures_n to build ensures2. *)
let COMBINE_ENSURES_N_ENSURES2 = prove(
  `!(step:S->S->bool) P Q C P2 Q2 C2 fn_1 fn_2.
      ensures_n step P Q C fn_1 /\ ensures_n step P2 Q2 C2 fn_2
      ==> ensures2 step (\(s,s2). P s /\ P2 s2)
                        (\(s',s2'). Q s' /\ Q2 s2')
                        (\(s,s2) (s',s2'). C s s' /\ C2 s2 s2') fn_1 fn_2`,
  REWRITE_TAC [ensures_n;ensures2;eventually_n] THEN MESON_TAC[]);;

(* Symmetricity for ensures2 *)
let ENSURES2_SYM = prove(
  `!(step:S->S->bool) P Q C fn_1 fn_2.
      ensures2 step P Q C fn_1 fn_2
      <=> ensures2 step (\(s,s2). P (s2,s))
                        (\(s',s2'). Q (s2',s'))
                        (\(s,s2) (s',s2'). C (s2,s) (s2',s')) fn_2 fn_1`,
  REWRITE_TAC [ensures2] THEN REPEAT STRIP_TAC THEN EQ_TAC THENL [
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (fun th -> MP_TAC (MATCH_MP th (ASSUME `(P:S#S->bool) (s2_init,s1_init)`))) THEN
    DISCH_TAC THEN MATCH_MP_TAC EVENTUALLY_N_SWAP THEN ASM_REWRITE_TAC[];

    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (fun th -> MP_TAC (MATCH_MP th (ASSUME `(P:S#S->bool) (s1_init,s2_init)`))) THEN
    DISCH_TAC THEN MATCH_MP_TAC EVENTUALLY_N_SWAP THEN ASM_REWRITE_TAC[]
  ]);;

(* Combine ensures_n and ensures2 *)
let ENSURES_N_ENSURES2_CONJ = prove(
  `!(step:S->S->bool) P1 Q1 C1 P Q C fn_1 fn_2.
      ensures_n step P1 Q1 C1 fn_1 /\
      ensures2 step P Q C fn_1 fn_2
      ==> ensures2 step (\(s,s2). P (s,s2) /\ P1 s)
                        (\(s',s2'). Q (s',s2') /\ Q1 s')
                        (\(s,s2) (s',s2'). C (s,s2) (s',s2') /\ C1 s s')
                        fn_1 fn_2`,
  REWRITE_TAC [ensures_n;ensures2;eventually_n] THEN MESON_TAC[]);;

(*  A transitivity rule for ENSURES2.
    Note that the num step functions of ensures2 must be constant functions
    in this lemma.
    In order to use this lemma, you will need to convert, e.g.,
      `ensures2 step (\s. ...) (..) (..) (\s. read X0 s)`
    into:
      `ensures2 step (\s. read X0 s = n /\ ...) (..) (..) (\s. n)`.
*)
let ENSURES2_TRANS = prove(
  `!(step:S->S->bool) P Q R C C' n1 n1' n2 n2'.
      ensures2 step P Q C (\s. n1) (\s. n1') /\
      ensures2 step Q R C' (\s. n2) (\s. n2')
      ==> ensures2 step P R (C ,, C') (\s. n1 + n2) (\s. n1' + n2')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures2] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (fun th -> ASSUME_TAC (MATCH_MP th (ASSUME `(P:S#S->bool) (s1_init,s2_init)`))) THEN
  SUBGOAL_THEN `!s1'' s2''.
    (Q:S#S->bool) (s1'',s2'') /\ (C:S#S->S#S->bool) (s1_init,s2_init) (s1'',s2'')
    ==> eventually_n (step:S->S->bool) n2
        (\s1'. eventually_n step n2'
                (\s2'. R (s1',s2') /\ (C ,, C') (s1_init,s2_init) (s1',s2')) s2'')
        s1''` ASSUME_TAC THENL [
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (fun th -> MP_TAC (MATCH_MP th (ASSUME `(Q:S#S->bool) (s1'',s2'')`))) THEN
    MATCH_MP_TAC EVENTUALLY_N_MONO THEN BETA_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC EVENTUALLY_N_MONO THEN BETA_TAC THEN GEN_TAC THEN
    REWRITE_TAC[seq] THEN ASM_MESON_TAC[];
    ALL_TAC
  ] THEN
  MATCH_MP_TAC EVENTUALLY_N_NESTED_COMPOSE THEN
  EXISTS_TAC `\s2' s1'. (Q:S#S->bool) (s1',s2') /\ (C:S#S->S#S->bool) (s1_init,s2_init) (s1',s2')` THEN
  ASM_REWRITE_TAC[]);;

let ENSURES2_FRAME_SUBSUMED = prove(
  `!(step:S->S->bool) P Q C C' fn1 fn2.
    C subsumed C' ==> ensures2 step P Q C fn1 fn2 ==> ensures2 step P Q C' fn1 fn2`,
  REWRITE_TAC[subsumed;ensures2;eventually_n] THEN
  MESON_TAC[]);;

let ENSURES2_WEAKEN = prove(
  `!(step:S->S->bool) P Q P' Q' C C' fn1 fn2.
    (!s s'. P'(s,s') ==> P(s,s')) /\
    (!s s'. Q(s,s') ==> Q'(s,s')) /\
    C subsumed C'
    ==> ensures2 step P Q C fn1 fn2
    ==> ensures2 step P' Q' C' fn1 fn2`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (fun th1 -> FIRST_X_ASSUM (fun th2 ->
    MP_TAC (MATCH_MP (MATCH_MP ENSURES2_FRAME_SUBSUMED th1) th2))) THEN
  REWRITE_TAC[ensures2] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `eventually_n (step:S->S->bool) (fn1 s1_init)
              (\s1'. eventually_n step (fn2 s2_init)
                     (\s2'. Q (s1',s2') /\ C' (s1_init,s2_init) (s1',s2'))
                     s2_init)
              s1_init` MP_TAC THENL [
    ASM_MESON_TAC[]; ALL_TAC
  ] THEN
  MATCH_MP_TAC EVENTUALLY_N_MONO THEN REWRITE_TAC[] THEN GEN_TAC THEN
  MATCH_MP_TAC EVENTUALLY_N_MONO THEN REWRITE_TAC[] THEN GEN_TAC THEN
  ASM_MESON_TAC[]);;

let ENSURES2_WEAKEN2 = prove(
  `!(step:S->S->bool) P Q P' Q' C C' fn1 fn2.
    (!s s'. P'(s,s') ==> P(s,s')) /\
    (!s s' s_init s_init'. P (s_init,s_init') /\ Q(s,s') /\
           C (s_init,s_init') (s,s')
      ==> Q'(s,s')) /\
    C subsumed C'
    ==> ensures2 step P Q C fn1 fn2
    ==> ensures2 step P' Q' C' fn1 fn2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN

  MP_TAC (ASSUME `(C:(S#S->S#S->bool)) subsumed C'`) THEN
  REWRITE_TAC[subsumed] THEN DISCH_TAC THEN
  REWRITE_TAC[ensures2] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `eventually_n (step:S->S->bool) (fn1 s1_init)
              (\s1'. eventually_n step (fn2 s2_init)
                     (\s2'. Q (s1',s2') /\ C (s1_init,s2_init) (s1',s2'))
                     s2_init)
              s1_init` MP_TAC THENL [
    ASM_MESON_TAC[]; ALL_TAC
  ] THEN
  MATCH_MP_TAC EVENTUALLY_N_MONO THEN REWRITE_TAC[] THEN GEN_TAC THEN
  MATCH_MP_TAC EVENTUALLY_N_MONO THEN REWRITE_TAC[] THEN GEN_TAC THEN
  ASM_MESON_TAC[]);;


(*  ENSURES2_TRANS but slightly relaxes constraints on the intermediate
    assertion Q and the final frame C ,, C'.
*)
let ENSURES2_TRANS_GEN = prove(
  `forall (step:S->S->bool) P Q Q' R C C' C'' n1 n1' n2 n2'.
      ensures2 step P Q C (\s. n1) (\s. n1') /\
      ensures2 step Q' R C' (\s. n2) (\s. n2') /\
      (forall s s'. Q(s,s') ==> Q'(s,s')) /\
      (C ,, C') subsumed C''
      ==> ensures2 step P R C'' (\s. n1 + n2) (\s. n1' + n2')`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (REWRITE_RULE [GSYM IMP_CONJ] ENSURES2_WEAKEN) THEN
  MAP_EVERY EXISTS_TAC [`P:S#S->bool`;`R:S#S->bool`;`(C:S#S->S#S->bool) ,, (C':S#S->S#S->bool)`] THEN
  REPEAT CONJ_TAC THENL [
    MESON_TAC[]; MESON_TAC[]; ASM_REWRITE_TAC[]; ALL_TAC
  ] THEN
  MATCH_MP_TAC ENSURES2_TRANS THEN
  EXISTS_TAC `Q:S#S->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (REWRITE_RULE [GSYM IMP_CONJ] ENSURES2_WEAKEN) THEN
  MAP_EVERY EXISTS_TAC [`Q':S#S->bool`;`R:S#S->bool`;`C':S#S->S#S->bool`] THEN
  ASM_REWRITE_TAC[SUBSUMED_REFL]);;

let ENSURES2_CONJ = prove(
  `!(step:S->S->bool) P Q P' Q' C fn1 fn2.
      ensures2 step P Q C fn1 fn2 /\
      ensures2 step P' Q' C fn1 fn2
      ==> ensures2 step
        (\(s,s'). P (s,s') /\ P' (s,s'))
        (\(s,s'). Q (s,s') /\ Q' (s,s'))
        C fn1 fn2`,

  REWRITE_TAC[ensures2;eventually_n] THEN MESON_TAC[]);;

let ENSURES2_CONJ_FRAME = prove
 (`forall (step:S->S->bool) P Q R nstep1 nstep2 f.
        (!s s2 s_final s_final2. R (s,s2) (s_final,s_final2)
           ==> (f s s2 <=> f s_final s_final2)) /\
        ensures2 step P Q R nstep1 nstep2
        ==> ensures2 step (\(s,s'). P (s,s') /\ f s s') (\(s,s'). Q (s,s') /\ f s s')
            R nstep1 nstep2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures2;eventually_n] THEN MESON_TAC[]);;

let ENSURES2_CONJ2 = prove(
  `!(step:S->S->bool) P Q P' Q' C1 C2 C3 fn1 fn2 fn3.
      ensures2 step P Q
        (\(s,s2) (s',s2'). C1 s s' /\ C2 s2 s2')
        fn1 fn2 /\
      ensures2 step P' Q'
        (\(s,s2) (s',s2'). C2 s s' /\ C3 s2 s2')
        fn2 fn3
      ==> ensures2 step
        (\(s,s'). ?s''. P (s,s'') /\ P' (s'',s'))
        (\(s,s'). ?s'''. Q (s,s''') /\ Q' (s''',s'))
        (\(s,s2) (s',s2'). C1 s s' /\ C3 s2 s2')
        fn1 fn3`,

  REWRITE_TAC[ensures2] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN (fun th -> let a,b = CONJ_PAIR th in
    REPEAT GEN_TAC THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM (fun th -> LABEL_TAC "H1" (MATCH_MP a th)) THEN
    FIRST_X_ASSUM (fun th -> LABEL_TAC "H2" (MATCH_MP b th))) THEN
  REMOVE_THEN "H1" (fun th -> REMOVE_THEN "H2" (fun th2 ->
    ASSUME_TAC (REWRITE_RULE [EVENTUALLY_N_P_INOUT] (CONJ th2 th)))) THEN
  FIRST_X_ASSUM MP_TAC THEN MATCH_MP_TAC EVENTUALLY_N_MONO THEN
  BETA_TAC THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `eventually_n (step:S->S->bool) (fn2 s'')
      (\s2'. eventually_n step (fn2 s'')
             (\s1''. eventually_n step (fn3 s2_init)
                    (\s2''. Q' (s1'',s2'') /\ C2 s'' s1'' /\ C3 s2_init s2'' /\
                            Q (s':S,s2') /\
                            (C1:S->S->bool) s1_init s' /\
                            C2 s'' s2')
                    s2_init)
             s'')
      s''` MP_TAC THENL [
    FIRST_X_ASSUM MP_TAC THEN
    MATCH_MP_TAC EVENTUALLY_N_MONO THEN REWRITE_TAC[] THEN GEN_TAC THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[CONJ_SYM] EVENTUALLY_N_P_INOUT] THEN
    MATCH_MP_TAC EVENTUALLY_N_MONO THEN REWRITE_TAC[] THEN GEN_TAC THEN
    MATCH_MP_TAC EVENTUALLY_N_MONO THEN MESON_TAC[];
    ALL_TAC
  ] THEN
  DISCH_THEN (fun th -> MP_TAC
    (MATCH_MP EVENTUALLY_N_SWAP (MATCH_MP EVENTUALLY_N_NESTED th))) THEN
  MATCH_MP_TAC EVENTUALLY_N_MONO THEN REWRITE_TAC[] THEN GEN_TAC THEN
  DISCH_THEN (fun th -> MAP_EVERY MP_TAC [th;MATCH_MP EVENTUALLY_N_STEPS th]) THEN
  MESON_TAC[eventually_n]);;


let ENSURES2_TRIVIAL = prove(
  `!(step:A->A->bool) P Q C.
    (!s. P s ==> Q s) /\ (!s. C s s) ==>
    ensures2 step P Q C (\s. 0) (\s. 0)`,

  REWRITE_TAC[ensures2;EVENTUALLY_N_TRIVIAL] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN MESON_TAC[]);;


(* ENSURES2_WHILE_PAUP_TAC verifies a relational hoare triple of two WHILE loops,
   whose induction variable increases from a to b.
   The loops should terminate at their backedges when the induction variables
   eventually become b.
   ENSURES_WHILE_PAUP_TAC takes the following arguments, all of which are HOL
   Light terms:
  - a: counter begin, has `:num` type
  - b: counter end (not inclusive), has `:num` type
  - pc1_head, pc1_backedge: program counter pointing to the beginning/end of
                            the loop of the first program, has `:num` type
  - pc2_head, pc2_backedge: program counter pointing to the beginning/end of
                            the loop of the second program, has `:num` type
  - loopinv: relational loop invariant, has `:num->S#S->bool` type where S is
             the type of a program state
  - flagcond1, flagcond2: `:num->S->bool` typed terms describing when loops
                          terminate. Typically involves a flag; e.g.,
                          `\(i:num) s. read ZF s <=> (word i:int64) = word n`
  - f_nsteps1, f_nsteps2: `:num->num`, the number of small steps taken inside
                          the loop bodies
  - nsteps_pre1, nsteps_pre2: `:num`, the number of small steps taken to reach
                              from precondition to the loop header
  - nsteps_post1, nsteps_post2: `:num`, the number of small steps taken to reach
                                from pc1_backedge,pc2_backedge to
                                postcondition
  - nsteps_backedge1, nsteps_backedge2:
      `:num`, the number of small steps that must be taken to 'take' backedges.
      These are typically 1, but you can do some clever tricks such as giving
      relation between rotated loops.
*)

let ENSURES2_WHILE_PAUP_TAC =
  let pth = prove(
    `!a b pc1_pre pc1 pc1' pc2_pre pc2 pc2'
            (loopinv:num->A->A->bool)
            (flagpred1:num->A->bool) (flagpred2:num->A->bool)
            (f_nsteps1:num->num) (f_nsteps2:num->num)
            (nsteps_pre1:num) (nsteps_pre2:num)
            (nsteps_post1:num) (nsteps_post2:num)
            (nsteps_backedge1:num) (nsteps_backedge2:num).
        C ,, C = C /\
        a < b /\
        ensures2 step
          (\(s,s2). program_decodes1 s /\ read pcounter s = (word pc1_pre:(N)word) /\
                    program_decodes2 s2 /\ read pcounter s2 = (word pc2_pre:(N)word) /\
                    precondition s s2)
          (\(s,s2). program_decodes1 s /\ read pcounter s = (word pc1) /\
                    program_decodes2 s2 /\ read pcounter s2 = (word pc2) /\
                    loopinv a s s2)
          C
          (\s. nsteps_pre1) (\s. nsteps_pre2) /\
        // loop body
        (!i. a <= i /\ i < b
            ==> ensures2 step
                (\(s,s2). program_decodes1 s /\ read pcounter s = word pc1 /\
                          program_decodes2 s2 /\ read pcounter s2 = word pc2 /\
                          loopinv i s s2)
                (\(s,s2). program_decodes1 s /\ read pcounter s = word pc1' /\
                          program_decodes2 s2 /\ read pcounter s2 = word pc2' /\
                          loopinv (i+1) s s2 /\ flagpred1 (i+1) s /\
                          flagpred2 (i+1) s2)
                C
                (\s. f_nsteps1 i) (\s. f_nsteps2 i)) /\
        // backedge taken
        (!i. a < i /\ i < b
            ==> ensures2 step
                (\(s,s2). program_decodes1 s /\ read pcounter s = word pc1' /\
                          program_decodes2 s2 /\ read pcounter s2 = word pc2' /\
                          loopinv i s s2 /\ flagpred1 i s /\ flagpred2 i s2)
                (\(s,s2). program_decodes1 s /\ read pcounter s = word pc1 /\
                          program_decodes2 s2 /\ read pcounter s2 = word pc2 /\
                          loopinv i s s2)
                C
                (\s. nsteps_backedge1) (\s. nsteps_backedge2)) /\
        // backedge not taken
        ensures2 step
            (\(s,s2). program_decodes1 s /\ read pcounter s = word pc1' /\
                      program_decodes2 s2 /\ read pcounter s2 = word pc2' /\
                      loopinv b s s2 /\ flagpred1 b s /\ flagpred2 b s2)
            postcondition
            C
            (\s. nsteps_post1) (\s. nsteps_post2) /\
        nsteps1 = nsteps_pre1 + (nsum(a..(b-1)) (\i. f_nsteps1 i) + (b-1-a) * nsteps_backedge1) +
                  nsteps_post1 /\
        nsteps2 = nsteps_pre2 + (nsum(a..(b-1)) (\i. f_nsteps2 i) + (b-1-a) * nsteps_backedge2) +
                  nsteps_post2
        ==> ensures2 step
            (\(s,s2). program_decodes1 s /\ read pcounter s = word pc1_pre /\
                      program_decodes2 s2 /\ read pcounter s2 = word pc2_pre /\
                      precondition s s2)
            postcondition
            C
            (\s. nsteps1) (\s. nsteps2)`,

  let APPLY_ENSURES2_TRANS_TAC:tactic =
    USE_THEN "HCC" (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
    MATCH_MP_TAC ENSURES2_TRANS THEN META_EXISTS_TAC THEN CONJ_TAC in
  REPEAT GEN_TAC THEN
  INTRO_TAC "HCC HBOUND HPRE HLOOP HBACKEDGE HPOST HNSTEPS1 HNSTEPS2" THEN
  REMOVE_THEN "HNSTEPS1" (fun th -> SUBST_ALL_TAC th) THEN
  REMOVE_THEN "HNSTEPS2" (fun th -> SUBST_ALL_TAC th) THEN
  (* precondition *)
  APPLY_ENSURES2_TRANS_TAC THENL [
    USE_THEN "HPRE" (fun th -> UNIFY_ACCEPT_TAC [`Q:(A#A)->bool`] th);
    ALL_TAC
  ] THEN
  (* postcondition *)
  APPLY_ENSURES2_TRANS_TAC THENL [
    ALL_TAC;
    USE_THEN "HPOST" (fun th -> UNIFY_ACCEPT_TAC [`Q:(A#A)->bool`] th)
  ] THEN
  (* the loop *)
  REMOVE_THEN "HPRE" (K ALL_TAC) THEN
  REMOVE_THEN "HPOST" (K ALL_TAC) THEN
  MAP_EVERY (fun s -> REMOVE_THEN s MP_TAC) ["HBOUND";"HLOOP";"HBACKEDGE"] THEN
  SPEC_TAC (`b:num`,`b:num`) THEN
  INDUCT_TAC THENL [
    ARITH_TAC;
    ALL_TAC
  ] THEN
  MAP_EVERY INTRO_TAC ["HBACKEDGE";"HLOOP";"HBOUND"] THEN
  ASM_CASES_TAC `a < b` THENL [
    ALL_TAC;
    (* a = b *)
    SUBGOAL_THEN `a:num = b` SUBST_ALL_TAC THENL [
      ASM_ARITH_TAC; ALL_TAC
    ] THEN
    REWRITE_TAC[SUC_SUB1;NSUM_SING_NUMSEG;SUB_REFL;ADD1] THEN
    GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o RAND_CONV)
      [(GSYM (snd (CONJ_PAIR SEQ_ID)))] THEN
    MATCH_MP_TAC ENSURES2_TRANS THEN
    META_EXISTS_TAC THEN
    CONJ_TAC THENL [
      USE_THEN "HLOOP" (fun th -> MP_TAC (SPEC `b:num` th)) THEN
      ANTS_TAC THENL [
        ARITH_TAC;
        DISCH_THEN (fun th -> UNIFY_ACCEPT_TAC  [`Q:(A#A)->bool`] th)
      ];

      REWRITE_TAC[ensures2;eventually_n;STEPS_TRIVIAL;ARITH_RULE`~(x<0)`;MULT] THEN MESON_TAC[]
    ]
  ] THEN

  SUBGOAL_THEN
    `!f x. nsum (a..SUC b - 1) (\i. f i) + (SUC b - 1 - a) * x =
           (nsum (a..b - 1) (\i. f i) + (b - 1 - a) * x) + x + f b`
      (fun th -> REWRITE_TAC[th]) THENL [
    REWRITE_TAC[ADD1;ADD_SUB;ETA_AX] THEN
    REWRITE_TAC[ARITH_RULE`(x+y)+z+w=(x+w)+y+z`] THEN
    IMP_REWRITE_TAC[GSYM NSUM_CLAUSES_RIGHT] THEN
    REWRITE_TAC[ARITH_RULE`p*q+q=(p+1)*q`] THEN
    SUBGOAL_THEN `b - 1 - a + 1=b-a` SUBST_ALL_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN
  APPLY_ENSURES2_TRANS_TAC THENL [
    ALL_TAC;

    APPLY_ENSURES2_TRANS_TAC THENL [
      REMOVE_THEN "HBACKEDGE" (fun th -> MP_TAC (SPEC `b:num` th)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (UNIFY_ACCEPT_TAC [`Q:(A#A)->bool`;`Q':(A#A)->bool`]);

      REWRITE_TAC[ADD1] THEN
      REMOVE_THEN "HLOOP" (fun th -> MP_TAC (SPEC `b:num` th)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th])
    ]
  ] THEN

  FIRST_X_ASSUM (fun th -> MATCH_MP_TAC(REWRITE_RULE[GSYM IMP_CONJ] th)) THEN
  REPEAT CONJ_TAC THENL [
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]
  ]) in

  fun a b pc1_head pc1_backedge pc2_head pc2_backedge
      loopinv flagcond1 flagcond2 f_nsteps1 f_nsteps2
      nsteps_pre1 nsteps_pre2
      nsteps_post1 nsteps_post2
      nsteps_backedge1 nsteps_backedge2 ->
    MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [a;b;pc1_head;pc1_backedge;pc2_head;pc2_backedge;
      loopinv;flagcond1;flagcond2;
      f_nsteps1;f_nsteps2;nsteps_pre1;nsteps_pre2;nsteps_post1;nsteps_post2;
      nsteps_backedge1;nsteps_backedge2] THEN
    CONJ_TAC THENL [
      (* MAYCHANGE. *)
      then_ (* apply multiple subgoals *)
      (REWRITE_TAC[FUN_EQ_THM] THEN
       REWRITE_TAC[FORALL_PAIR_THM] THEN
       REWRITE_TAC[SEQ_PAIR_SPLIT] THEN
       REWRITE_TAC[ETA_AX] THEN
       REPEAT STRIP_TAC)
      ((MATCH_MP_TAC (MESON[] `!(p:A->A->bool) (q:A->A->bool) r s.
        ((p = r) /\ (q = s)) ==> (p x1 x2 /\ q y1 y2 <=> r x1 x2 /\ s y1 y2)`) THEN
        REWRITE_TAC[ETA_AX] THEN
        REPEAT (CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC]) THEN
        MAYCHANGE_IDEMPOT_TAC)
        ORELSE
        (* a simpler case *)
        (REWRITE_TAC[seq;EXISTS_PAIR_THM] THEN NO_TAC));

      (* The remaining condition. *)
      ALL_TAC
    ];;

(* A relational hoare triple version of ENSURES_INIT_TAC. *)
let ENSURES2_INIT_TAC sname sname2 =
  GEN_REWRITE_TAC I [ensures2] THEN
  REWRITE_TAC[] (* for general beta reduction *) THEN
  W(fun (asl,w) ->
        let ty = type_of(fst(dest_forall w)) in
        let svar = mk_var(sname,ty) in
        let svar2 = mk_var(sname2,ty) in
        MAP_EVERY X_GEN_TAC [svar;svar2] THEN
        DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
        ASSUME_TAC(ISPEC svar MAYCHANGE_STARTER) THEN
        ASSUME_TAC(ISPEC svar2 MAYCHANGE_STARTER));;

let APPLY_IF (checker:term->bool) (t:tactic) =
  W (fun (asl,g) ->
    if checker g then t else ALL_TAC);;


(* ------------------------------------------------------------------------- *)
(* A useful tactic that proves a conjunction of MAYCHANGEs.                  *)
(* ------------------------------------------------------------------------- *)

let MONOTONE_MAYCHANGE_CONJ_TAC =
  W (fun (asl,w) ->
    let maychange1,maychange2 = dest_conj w in
    let _,s0 = let c,_ = dest_comb maychange1 in dest_comb c in
    let _,s0' = let c,_ = dest_comb maychange2 in dest_comb c in
    CONJ_TAC THENL [
      (* MAYCHANGE of the left program *)
      (DISCARD_ASSUMPTIONS_TAC (fun th -> free_in s0' (concl th)) THEN
        MONOTONE_MAYCHANGE_TAC) ORELSE
      (* for MAYCHANGE s s' where s = s' *)
      (ASSUME_TAC (ISPECL [s0] MAYCHANGE_STARTER) THEN MONOTONE_MAYCHANGE_TAC);

      (* MAYCHANGE of the right program *)
      (DISCARD_ASSUMPTIONS_TAC (fun th -> free_in s0 (concl th)) THEN
        MONOTONE_MAYCHANGE_TAC) ORELSE
      (* for MAYCHANGE s s' where s = s' *)
      (ASSUME_TAC (ISPECL [s0'] MAYCHANGE_STARTER) THEN MONOTONE_MAYCHANGE_TAC)
    ]);;
