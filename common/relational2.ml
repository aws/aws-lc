(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(*    Relational Hoare Logic for proving program equivalence.                *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* A definition of steps and its properties.                                 *)
(* ------------------------------------------------------------------------- *)

let steps_RULES,steps_INDUCT,steps_CASES = new_inductive_definition
  `(!s. steps (step:S->S->bool) 0 (s:S) (s:S)) /\
   (!s s'' n. (?s'. step s s' /\ steps step n s' s'') ==> steps step (n+1) s s'')`;;

let STEPS_TRIVIAL = prove(
  `!(s:S) s' step. steps step 0 s s' <=> s = s'`,
  ONCE_REWRITE_TAC[steps_CASES] THEN REWRITE_TAC[ARITH_RULE`~(0=n+1)`] THEN MESON_TAC[]);;

(* Trivial, but to help pattern matcher... *)
let STEPS_SYM = prove(
  `!(step:S->S->bool) m n s s'. steps step (m+n) s s' <=> steps step (n+m) s s'`,
  REWRITE_TAC[ADD_SYM]);;

let STEPS_STEP_LEFT_RIGHT = prove(
  `!(step:S->S->bool) n s s'.
      (?s''. step s s'' /\ steps step n s'' s') <=> (?s''. steps step n s s'' /\ step s'' s')`,
  GEN_TAC THEN
  MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL [
    MESON_TAC[STEPS_TRIVIAL];

    REPEAT STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE`SUC n=1+n`] THEN
    ONCE_REWRITE_TAC [steps_CASES] THEN
    REWRITE_TAC[ARITH_RULE`~(1+n = 0)`] THEN
    SUBGOAL_THEN `!k (P:num->bool). (?n'. 1+k = n'+1 /\ P n') <=> P k`
        (fun th -> REWRITE_TAC[th]) THENL [
      REPEAT GEN_TAC THEN EQ_TAC THENL [
        REPEAT STRIP_TAC THEN
        SUBGOAL_THEN `k:num=n'` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[ADD_SYM];

        REPEAT STRIP_TAC THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[ADD_SYM]
      ];
      ALL_TAC
    ] THEN
    let tt1 = `!P Q. (?a. P a /\ (?b. Q a b)) <=> (?a b. P a /\ Q a b)` in
    let tt2 = `!P Q. (?a. (?b. Q a b) /\ P a) <=> (?a b. Q a b /\ P a)` in
    REWRITE_TAC(map ITAUT [tt1;tt2]) THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    let tt3 = `!P Q. (?b a. P a /\ Q a b) <=> (?a. P a /\ (?b. Q a b))` in
    REWRITE_TAC[ITAUT tt3] THEN
    ASM_MESON_TAC[]
  ]);;

let STEPS_ADD =
  let lemma = prove(`!k (P:num->bool). (?n'. k+1 = n'+1 /\ P n') <=> P k`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `k:num=n'` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[];

    REPEAT STRIP_TAC THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]
  ]) in
  prove(
    `!(step:S->S->bool) m n s s'.
    steps step (m+n) s s' <=> ?s''. steps step m s s'' /\ steps step n s'' s'`,
    REPEAT_N 2 GEN_TAC THEN
    MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL [
      REWRITE_TAC[ADD_0;STEPS_TRIVIAL] THEN MESON_TAC[];

      REWRITE_TAC[ARITH_RULE`m + SUC n = (m + n) + 1`;ARITH_RULE`SUC n = n + 1`] THEN
      REPEAT STRIP_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [steps_CASES] THEN
      ASM_REWRITE_TAC[ARITH_RULE`!m n. ~((m+n)+1 = 0)`;lemma] THEN
      SUBGOAL_THEN `!(s'':S).
          (steps (step:S->S->bool) (n + 1) s'' s' <=>
          ?s'''. step s'' s''' /\ steps step n s''' s')`
          (fun th -> REWRITE_TAC[th]) THENL [
        REPEAT STRIP_TAC THEN
        GEN_REWRITE_TAC LAND_CONV [steps_CASES] THEN
        REWRITE_TAC[ARITH_RULE`!n. ~(n+1=0)`;lemma];
        ALL_TAC
      ] THEN
      REWRITE_TAC[CONJ_ASSOC;
        ITAUT `!P Q. (?a. P a /\ (?b. Q a b)) <=> (?a b. P a /\ Q a b)`;
        ITAUT `!P Q. (?a b. P a b /\ Q b) <=> (?b. (?a. P a b) /\ Q b)`] THEN
      REWRITE_TAC[STEPS_STEP_LEFT_RIGHT]
    ]);;

(* Again trivial, but for pattern matching... *)
let STEPS_STEP = prove(
  `!n (s:S) s' step.
     steps step (1+n) s s' <=> ?s''. step s s'' /\ steps step n s'' s'`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [steps_CASES] THEN
  REWRITE_TAC[ARITH_RULE`~(1+n=0)`] THEN
  EQ_TAC THENL [
    STRIP_TAC THEN
    SUBGOAL_THEN `n:num = n'` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[];

    STRIP_TAC THEN
    EXISTS_TAC `n:num` THEN
    REWRITE_TAC[ADD_SYM] THEN ASM_MESON_TAC[]]);;

let STEPS_ONE = prove(
  `!(s:S) s' step. steps step 1 s s' <=> step s s'`,
  METIS_TAC[ARITH_RULE`1=1+0`;STEPS_STEP;STEPS_TRIVIAL]);;

let STEPS_NOSTUCK = prove(
  `!(step:S->S->bool) (n:num) (s:S).
    (!s' n'. (n' < n /\ steps step n' s s') ==> ?s''. step s' s'')
    ==> ?s'. steps step n s s'`,
  GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL [
    MESON_TAC[STEPS_TRIVIAL];

    REPEAT STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE`SUC n=1+n`;STEPS_STEP;STEPS_STEP_LEFT_RIGHT] THEN
    SUBGOAL_THEN
        `(!(s':S) n'. (n' < n /\ steps (step:S->S->bool) n' s s' ==> (?s''. step s' s''))) /\
        (!(s':S). steps (step:S->S->bool) n s s' ==> (?s''. step s' s''))`
        MP_TAC THENL [
      CONJ_TAC THENL [
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC`n':num` THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;

        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC`n:num` THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC
      ];
      ALL_TAC
    ] THEN
    DISCH_THEN (fun th -> let th1,th2 = CONJ_PAIR th in
      LABEL_TAC "H1" th1 THEN LABEL_TAC "H2" th2) THEN
    SUBGOAL_THEN `?(s':S). steps step n s s'` MP_TAC THENL [
      ASM_MESON_TAC[]; ALL_TAC
    ] THEN STRIP_TAC THEN
    ASM_MESON_TAC[]
  ]);;


(* ------------------------------------------------------------------------- *)
(* A relational hoare triple 'ensures2'. It is defined using 'eventually_n'. *)
(* ------------------------------------------------------------------------- *)

let eventually_n = new_definition
  `eventually_n (step:S->S->bool) (n:num) (P:S->bool) s <=>
   ((!s'. steps step n s s' ==> P s') /\
    // There isn't a 'stuck' state at the end of a trace shorter than n
    (!s' n'. (n' < n /\ steps step n' s s') ==> ?s''. step s' s''))`;;

(* Define relational hoare triples using eventually_n. *)
let ensures2 = new_definition
  `ensures2 (step:S->S->bool) (precond:S#S->bool) (postcond:S#S->bool) (frame:S#S->S#S->bool)
            (step_calc1:S->num) (step_calc2:S->num) <=>
  !(s1:S) (s2:S). precond (s1,s2)
      ==> eventually_n step (step_calc1 s1)
            (\s1'. eventually_n step (step_calc2 s2)
                (\s2'. postcond (s1',s2') /\ frame (s1,s2) (s1',s2')) s2) s1`;;

(* eventually_n version of ensures. *)
let ensures_n = new_definition
  `ensures_n (step:S->S->bool) (precond:S->bool) (postcond:S->bool) (frame:S->S->bool)
             (step_calc:S->num) <=>
    !s. precond s ==> eventually_n step (step_calc s) (\s'. postcond s' /\ frame s s') s`;;


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
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EVENTUALLY_STOP_TAC THEN ASM_REWRITE_TAC[];

    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL [
      EVENTUALLY_STOP_TAC THEN EVENTUALLY_STOP_TAC THEN ASM_REWRITE_TAC[];

      EVENTUALLY_NEXT_TAC THEN ASM_REWRITE_TAC[] THEN
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
(* Properties of eventually_n                                                *)
(* ------------------------------------------------------------------------- *)

let EVENTUALLY_N_TRIVIAL = prove(
  `!(step:S->S->bool) s (P:S->bool). eventually_n step 0 P s <=> P s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eventually_n;ARITH_RULE`!x. ~(x<0)`] THEN
  MESON_TAC[STEPS_TRIVIAL]);;

let EVENTUALLY_N_CONJ = prove(
  `!(step:S->S->bool) (P:S->bool) (Q:S->bool) n s.
    eventually_n step n P s /\ eventually_n step n Q s ==>
    eventually_n step n (\s. P s /\ Q s) s`,
  REWRITE_TAC[eventually_n] THEN MESON_TAC[]);;

let EVENTUALLY_N_SWAP = prove(
  `!(step:S->S->bool) s1 s2 n m (P:S->S->bool).
   eventually_n step n (\s1'. eventually_n step m (\s2'. P s1' s2') s2) s1 ==>
   eventually_n step m (\s2'. eventually_n step n (\s1'. P s1' s2') s1) s2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eventually_n] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[STEPS_NOSTUCK]);;

let EVENTUALLY_N_COMPOSE =
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

let EVENTUALLY_N_STEP =
  prove(
    `!(step:S->S->bool) (P:S->bool) n s.
      eventually_n step (1+n) P s <=>
      ((?s'. step s s') /\
       (!s'. step s s' ==> eventually_n step n P s'))`,
    REWRITE_TAC[eventually_n;STEPS_ADD;STEPS_ONE] THEN
    REPEAT STRIP_TAC THEN EQ_TAC THENL [
      REPEAT STRIP_TAC THENL [
        FIRST_X_ASSUM (fun th -> MP_TAC (SPECL [`s:S`;`0`] th)) THEN
        MESON_TAC[ARITH_RULE`0<1+n`; STEPS_TRIVIAL];

        ASM_MESON_TAC[];

        FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `1+n':num` THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_MESON_TAC[STEPS_STEP]
      ];

      REPEAT STRIP_TAC THENL [
        ASM_MESON_TAC[];

        MP_TAC (SPEC `n':num` num_CASES) THEN
        STRIP_TAC THENL [
          ASM_MESON_TAC[STEPS_TRIVIAL];
          UNDISCH_TAC `n' = SUC n''` THEN REWRITE_TAC[ARITH_RULE`!k. SUC k = 1+k`] THEN
          DISCH_THEN SUBST_ALL_TAC THEN
          RULE_ASSUM_TAC (REWRITE_RULE[STEPS_ADD;STEPS_ONE]) THEN
          SUBGOAL_THEN `n''<n` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
          ASM_MESON_TAC[]
        ]
      ]
    ]);;

let EVENTUALLY_N_STEPS =
  prove(
    `!(step:S->S->bool) P (n:num) s. eventually_n step n P s ==> ?s'. steps step n s s'`,
    MESON_TAC[eventually_n;STEPS_NOSTUCK]);;

let EVENTUALLY_N_MONO =
  prove(
    `!(step:S->S->bool) (P:S->bool) (Q:S->bool) n s.
      (!s'. P s' ==> Q s') ==>
      eventually_n step n P s ==> eventually_n step n Q s`,
    REWRITE_TAC[eventually_n] THEN MESON_TAC[])

let EVENTUALLY_N_EVENTUALLY =
  prove(
    `!(step:S->S->bool) (P:S->bool) n s.
      eventually_n step n P s ==> eventually step P s`,
    REPEAT_N 2 GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL [
      REWRITE_TAC[eventually_n; STEPS_TRIVIAL] THEN
      ONCE_REWRITE_TAC[eventually_CASES] THEN MESON_TAC[];

      REWRITE_TAC[ARITH_RULE`SUC n=1+n`] THEN
      REPEAT STRIP_TAC THEN
      FIRST_ASSUM(fun th -> MP_TAC (GEN_REWRITE_RULE I [EVENTUALLY_N_STEP] th)) THEN
      STRIP_TAC THEN
      ONCE_REWRITE_TAC[eventually_CASES] THEN
      DISJ2_TAC THEN
      UNDISCH_TAC `eventually_n (step:S->S->bool) (1+n) P s` THEN
      REWRITE_TAC[eventually_n;STEPS_ADD;STEPS_ONE] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM (fun th -> MP_TAC (MATCH_MP STEPS_NOSTUCK th)) THEN
      STRIP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[STEPS_ADD;STEPS_ONE]) THEN
      ASM_MESON_TAC[eventually_n]
    ]);;

let EVENTUALLY_N_P_INOUT = prove(
  `!(step:S->S->bool) P Q n s0.
    P /\ eventually_n step n (\s. Q s s0) s0 <=>
    eventually_n step n (\s. P /\ Q s s0) s0`,
  REWRITE_TAC[eventually_n] THEN REPEAT STRIP_TAC THEN EQ_TAC THEN
  MESON_TAC[STEPS_NOSTUCK]);;

(* Inverse direction of this lemma (EVENTUALLY_N_EVENTUALLY_STEPS) is not true.
   Consider three states s0, s1, s2 that forms a triangle:
   (1) s0 -> s1 -> s2
   (2) s0 -> s2
   If P(s2) is true and P(s1) is false, then
   `eventually step (\s'. steps step 1 s s' /\ P s') s0` is true because
   `steps step 1 s0 s0` holds.
   However, `eventually_n step 1 P s` is false because P(s1) is false. *)
let EVENTUALLY_N_EVENTUALLY_STEPS = prove(
  `!(step:S->S->bool) P n s.
    eventually_n step n P s ==> eventually step (\s'. steps step n s s' /\ P s') s`,

  REPEAT_N 2 GEN_TAC THEN INDUCT_TAC THENL [
    REWRITE_TAC[eventually_n] THEN
    ONCE_REWRITE_TAC[eventually_CASES] THEN
    REWRITE_TAC[STEPS_TRIVIAL;ARITH_RULE`!n. ~(n<0)`] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_MESON_TAC[];

    REWRITE_TAC[ARITH_RULE`SUC n = 1 + n`] THEN
    GEN_TAC THEN
    DISCH_THEN (fun th -> MP_TAC (GEN_REWRITE_RULE I [EVENTUALLY_N_STEP] th)) THEN
    STRIP_TAC THEN ONCE_REWRITE_TAC[eventually_CASES] THEN DISJ2_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[STEPS_ADD;STEPS_ONE] THEN GEN_TAC THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM (fun evth -> ASSUME_TAC (MATCH_MP evth (ASSUME `(step:S->S->bool) s s''`))) THEN
    REWRITE_TAC[ITAUT`((?(x:S). P x) /\ Q) <=> (?x. P x /\ Q)`] THEN
    MATCH_MP_TAC EVENTUALLY_EXISTS THEN
    REWRITE_TAC[GSYM CONJ_ASSOC;GSYM EVENTUALLY_P_INOUT] THEN
    EXISTS_TAC `s'':S` THEN ASM_MESON_TAC[]
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
(* Properties of ensures_n, ensures2_n.                                      *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_ENSURES = prove(
  `!(step:S->S->bool) P Q C f_n.
      ensures_n step P Q C f_n ==> ensures step P Q C`,
  REWRITE_TAC[ensures_n;ensures] THEN ASM_MESON_TAC[EVENTUALLY_N_EVENTUALLY]);;

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
    FIRST_X_ASSUM (fun th -> MP_TAC (MATCH_MP th (ASSUME `(P:S#S->bool) (s2,s1)`))) THEN
    DISCH_TAC THEN MATCH_MP_TAC EVENTUALLY_N_SWAP THEN ASM_REWRITE_TAC[];

    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (fun th -> MP_TAC (MATCH_MP th (ASSUME `(P:S#S->bool) (s1,s2)`))) THEN
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

(*  Transitivity rule for ENSURES2.
    Note that the num step functions of ensures2 must be a constant function.
    In order to use this lemma, you will need to convert
      `ensures2 step (\s. read X0 s = n /\ ...) (..) (..) (\s. read X0 s)`
    into:
      `ensures2 step (\s. read X0 s = n /\ ...) (..) (..) (\s. n)`
    and apply this lemma.
*)
let ENSURES2_TRANS = prove(
  `!(step:S->S->bool) P Q R C C' n1 n1' n2 n2'.
      ensures2 step P Q C (\s. n1) (\s. n1') /\
      ensures2 step Q R C' (\s. n2) (\s. n2')
      ==> ensures2 step P R (C ,, C') (\s. n1 + n2) (\s. n1' + n2')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures2] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (fun th -> ASSUME_TAC (MATCH_MP th (ASSUME `(P:S#S->bool) (s1,s2)`))) THEN
  SUBGOAL_THEN `!s1'' s2''.
    (Q:S#S->bool) (s1'',s2'') /\ (C:S#S->S#S->bool) (s1,s2) (s1'',s2'')
    ==> eventually_n (step:S->S->bool) n2
        (\s1'. eventually_n step n2'
                (\s2'. R (s1',s2') /\ (C ,, C') (s1,s2) (s1',s2')) s2'')
        s1''` ASSUME_TAC THENL [
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (fun th -> MP_TAC (MATCH_MP th (ASSUME `(Q:S#S->bool) (s1'',s2'')`))) THEN
    MATCH_MP_TAC EVENTUALLY_N_MONO THEN BETA_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC EVENTUALLY_N_MONO THEN BETA_TAC THEN GEN_TAC THEN
    REWRITE_TAC[seq] THEN ASM_MESON_TAC[];
    ALL_TAC
  ] THEN
  MATCH_MP_TAC EVENTUALLY_N_COMPOSE THEN
  EXISTS_TAC `\s2' s1'. (Q:S#S->bool) (s1',s2') /\ (C:S#S->S#S->bool) (s1,s2) (s1',s2')` THEN
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
  SUBGOAL_THEN `eventually_n (step:S->S->bool) (fn1 s1)
              (\s1'. eventually_n step (fn2 s2)
                     (\s2'. Q (s1',s2') /\ C' (s1,s2) (s1',s2'))
                     s2)
              s1` MP_TAC THENL [
    ASM_MESON_TAC[]; ALL_TAC
  ] THEN
  MATCH_MP_TAC EVENTUALLY_N_MONO THEN REWRITE_TAC[] THEN GEN_TAC THEN
  MATCH_MP_TAC EVENTUALLY_N_MONO THEN REWRITE_TAC[] THEN GEN_TAC THEN
  ASM_MESON_TAC[]);;

let ENSURES2_CONJ = prove(
  `!(step:S->S->bool) P Q P' Q' C fn1 fn2.
      ensures2 step P Q C fn1 fn2 /\
      ensures2 step P' Q' C fn1 fn2
      ==> ensures2 step
        (\(s,s'). P (s,s') /\ P' (s,s'))
        (\(s,s'). Q (s,s') /\ Q' (s,s'))
        C fn1 fn2`,

  REWRITE_TAC[ensures2;eventually_n] THEN MESON_TAC[]);;

let EVENTUALLY_N_NESTED = prove(
  `!(step:S->S->bool) (s0:S).
    eventually_n step n (\s. eventually_n step n (\s2. P s s2) s0) s0 ==>
    eventually_n step n (\s. P s s) s0`,
  REWRITE_TAC[eventually_n] THEN
  REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[]);;

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
             (\s1''. eventually_n step (fn3 s2)
                    (\s2''. Q' (s1'',s2'') /\ C2 s'' s1'' /\ C3 s2 s2'' /\
                            Q (s':S,s2') /\
                            (C1:S->S->bool) s1 s' /\
                            C2 s'' s2')
                    s2)
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
        ASSUME_TAC(ISPEC svar MAYCHANGE_STARTER));;


let SEQ_PAIR_SPLIT = prove(
  `!(P:A->A->bool) (Q:A->A->bool) (R:A->A->bool) (S:A->A->bool) p1 p2 p1' p2'.
    ((\(s,s2) (s',s2'). P s s' /\ Q s2 s2') ,, (\(s,s2) (s',s2'). R s s' /\ S s2 s2'))
    (p1,p2) (p1',p2')
    <=>
    ((P ,, R) p1 p1' /\ (Q ,, S) p2 p2')`,
  REWRITE_TAC[seq;EXISTS_PAIR_THM] THEN MESON_TAC[]);;
