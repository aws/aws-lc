(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0 *)

Set Implicit Arguments.

Require Import SetoidClass.
Require Import List.
Require Import Permutation.
Require Import ZArith.BinInt.
Require Import Nat.
Require Import Arith.
Require Import Arith.Peano_dec.
Require Import Arith.Compare_dec.
Require Import micromega.Lia.

From EC Require Import GroupMulWNAF.
From EC Require Import WindowedMulMachine.


(* The precomputed generator multiplication algorithm is essentially the same as the wnaf multiplication algorithm, except:
1. In addition to the pre-computation of [1G, 3G, ... 31G] that are used for a single window, also precompute tables of larger values like 
[1*2^20G, 3*2^20G, ..., 31*2^20G]. In the general multiplication algorithm, these multiples would have been computed by 
doubling the accumulator in between windows. In the precomputed generator algorithm, we avoid some of this doubling and add in the pre-computed
values. We only need to double to get from one group to the next. E.g. with a window size of 5, and with 4 groups, we only need to double 20 times. 
2. Change the order so that each precomputed subtable is used at the beginning to produce a value that is added to the accumulator, 
and then the accumulator is doubled wsize times. 
*)

(* This file contains the proof of correctness for this algorithm. It uses the general purpose windowed multiplication machine
to transform the wnaf multiplication algorithm into the algorithm above. *)

Section GeneratorMul.

  Context `{dbl_grp : CommutativeGroupWithDouble}.

  Variable RegularWindow : SignedWindow -> Prop.
  Variable wsize : nat.
  Hypothesis wsize_nz : wsize <> 0%nat.
  Variable numWindows : nat.
  Hypothesis numWindows_nz : numWindows <> 0%nat.

  Variable p : GroupElem.
  Variable numPrecompExponentGroups : nat.
  Hypothesis numPrecompExponentGroups_nz : numPrecompExponentGroups <> O.
  Variable precompTableSize : nat.

  Definition OddWindow := OddWindow wsize.
  Variable pMultiple : SignedWindow -> GroupElem.
  Hypothesis pMultiple_correct : forall w,
    OddWindow w ->
    pMultiple w == groupMul_doubleAdd_signed w p.

  Definition groupMul_signedWindows := groupMul_signedWindows wsize pMultiple.
  Definition groupMul_signedWindows_prog := groupMul_signedWindows_prog p wsize.
  Definition evalWindowMult := evalWindowMult p wsize.

  (* Start with an algorithm that performs the computation in the correct order, but doesn't do any table lookups. 
  This is the basic odd signed window multiplication operation with the additions permuted, and with some accumulator 
  doublings inserted. *)
  Definition groupedMul d ws :=
    match (permuteAndDouble ws d (flatten (groupIndices numWindows numPrecompExponentGroups)) (endIndices (groupIndices numWindows numPrecompExponentGroups))) with
    | None => None
    | Some ps => Some (groupMul_signedWindows_prog ps)
    end.

  Theorem groupedMul_correct : forall ws d x,
    length ws = numWindows -> 
    Forall OddWindow ws -> 
    groupedMul d ws = Some x -> 
    groupMul_signedWindows ws == x.

    intros.
    unfold groupedMul in *.
    optSomeInv.
    unfold groupMul_signedWindows.
    rewrite <- permuteAndDouble_equiv; try apply H2; eauto.
    reflexivity.
    eapply Permutation_sym.
    eapply groupIndices_perm.
    apply numPrecompExponentGroups_nz.

  Qed.

  (* Use precomputed table for all additions *)
  Variable pExpMultiple : nat -> SignedWindow -> GroupElem.
  Hypothesis pExpMultiple_correct : forall n w,
    (n < precompTableSize)%nat -> 
    OddWindow w ->
    pExpMultiple n w == groupMul_doubleAdd_signed (Z.shiftl w (Z.of_nat (numPrecompExponentGroups * wsize * n))) p.

  (* An alternative semantics for double/add operations that perform all additions by a table lookup. If the required value is not
  in the table, then the operation fails. *)
  Definition evalWindowMult_precomp(p : GroupElem) (m : WindowedMultOp) (e : GroupElem) :=
  match m with
  | wm_Add n w => 
    if (divides numPrecompExponentGroups n) then (Some (groupAdd (pExpMultiple (Nat.div n numPrecompExponentGroups) w) e)) else None
  | wm_Double n => Some (groupDouble_n (n * wsize) e)
  end.

  (* Evaluate a double/add program using table lookups of addition operations. *)
  Fixpoint groupMul_signedWindows_precomp (e : GroupElem)(ws : list WindowedMultOp) : option GroupElem :=
    match ws with
    | nil => Some e
    | w :: ws' => match (groupMul_signedWindows_precomp e ws') with
      | None => None
      | Some x => 
        evalWindowMult_precomp p w x
      end
    end.

  (* Convert a simple windowed multiplication by permuting the addition operations and inserting doublings in a specific way. Then 
  run the double/add program using the semantics that performs all add operations by table lookup. This will only succeed 
  if doublings were inserted in a way that ensures all the add operations can be performed by table lookups. For example,
  we can permute the numbers [0, 1, 2, 3, ...] (describing the position of each window) to get [0, 4, 8, ..., 1, 5, 9, ..., 2, 6, 10, ....]
  and then insert a doubling after each part to decrease the following values by 1. This will result in a list where additions have 
  exponents that look like [0, 4, 8, ..., 0, 4, 8, ..., 0, 4, 8, ...]. These additions can be calculated using table lookups into a table
  that only includes multiples of 2^0, 2^4, 2^8, etc. *)
  Definition groupedMul_precomp d ws :=
    match (permuteAndDouble ws d (flatten (groupIndices numWindows numPrecompExponentGroups)) (endIndices (groupIndices numWindows numPrecompExponentGroups))) with
    | None => None
    | Some ps => (groupMul_signedWindows_precomp idElem ps)
    end.

  
  Definition ProgOddWindow (a : WindowedMultOp) :=
    match a with | wm_Add n w => (n < numPrecompExponentGroups * precompTableSize)%nat /\ OddWindow w | _ => True end.

  Theorem evalWindowMult_precomp_equiv : forall a g x,
    ProgOddWindow a ->
    evalWindowMult_precomp p a g = Some x ->
    evalWindowMult a g == x.

    unfold evalWindowMult_precomp, evalWindowMult.
    intros.
    destruct a; simpl in *.
    destruct(divides numPrecompExponentGroups n).
    inversion H0; clear H0; subst.
    rewrite pExpMultiple_correct.
    eapply groupAdd_proper; eauto.
    match goal with
    | [|- ?f ?a ?c == ?f ?b ?c] => replace a with b
    end.
    reflexivity.
    unfold zDouble_n.
    f_equal. 
    f_equal.
    rewrite <- Nat.mul_assoc.
    rewrite (Nat.mul_comm wsize).
    rewrite Nat.mul_assoc.
    f_equal.
    rewrite Nat.mul_comm.
    rewrite <- e at 1.
    rewrite Nat.gcd_comm.
    rewrite Nat.lcm_equiv2.
    rewrite Nat.gcd_comm.
    rewrite e.
    apply Nat.div_mul.
    lia.
    rewrite Nat.gcd_comm.
    lia.
    reflexivity.
    intuition idtac.
    eapply Nat.div_lt_upper_bound.
    lia.
    lia.
    intuition idtac.

    discriminate.
    inversion H0; clear H0; subst.
    reflexivity.
    
  Qed.

  Theorem groupMul_signedWindows_precomp_equiv : forall l x, 
    Forall ProgOddWindow l -> 
    groupMul_signedWindows_precomp idElem l = Some x ->
    groupMul_signedWindows_prog l == x.

    induction l; intros; simpl in *.
    inversion H0; clear H0; subst.
    reflexivity.
    case_eq (groupMul_signedWindows_precomp idElem l ); intros;
    rewrite H1 in H0.
    transitivity (evalWindowMult a g).
    eapply evalWindowMult_compat; eauto.
    eapply IHl.
    inversion H; clear H; subst.
    trivial.
    trivial.
    eapply evalWindowMult_precomp_equiv.
    inversion H; clear H; subst.
    trivial.
    eauto.
    discriminate.
    
  Qed.

  Theorem decrExp_OddWindow : forall x a y, 
    ProgOddWindow a -> 
    (decrExp x a) = Some y ->
    ProgOddWindow y.

    intros.
    unfold decrExp, ProgOddWindow in *.
    destruct a; simpl in *.
    destruct (le_dec x n).
    inversion H0; clear H0; subst.
    intuition idtac.
    lia.
    discriminate.
    inversion H0; clear H0; subst.
    trivial.

  Qed.

  Theorem decrExpLs_OddWindow : forall l0 x l1, 
    Forall ProgOddWindow l0 -> 
    decrExpLs x l0 = Some l1 ->
    Forall ProgOddWindow l1.

    induction l0; intros; simpl in *.
    inversion H0; clear H0; subst.
    econstructor.
    case_eq (decrExp x a); intros;
    rewrite H1 in H0.
    inversion H; clear H; subst.
    case_eq (decrExpLs x l0); intros;
    rewrite H in H0.
    inversion H0; clear H0; subst.
    econstructor; eauto.  
    eapply decrExp_OddWindow; eauto.
    discriminate.
    discriminate.

  Qed.

  Theorem insertDoubleAt_OddWindow : forall z x l0 l,
    Forall ProgOddWindow l0 -> 
    insertDoubleAt x l0 z = Some l ->
    Forall ProgOddWindow l.

    induction z; intros; simpl in *.
    replace (insertDoubleAt x l0 O) with (insertDouble x l0) in H0.
    unfold insertDouble in *.
    case_eq (decrExpLs  x l0); intros;
    rewrite H1 in H0.
    inversion H0; clear H0; subst.
    econstructor.
    apply I.
    eapply decrExpLs_OddWindow; eauto.
    discriminate.
    destruct l0; simpl in *.
    reflexivity.
    reflexivity.
    destruct l0; simpl in *.
    discriminate.
    case_eq (insertDoubleAt x l0 z); intros;
    rewrite H1 in H0.
    inversion H0; clear H0; subst.
    inversion H; clear H; subst.
    econstructor.
    trivial.
    eauto.
    discriminate.

  Qed.

  Theorem insertDoublesAt_OddWindow : forall z x l0 l,
    Forall ProgOddWindow l0 -> 
    insertDoublesAt x l0 z = Some l ->
    Forall ProgOddWindow l.

    induction z; intros; simpl in *.
    inversion H0; clear H0; subst.
    trivial.

    case_eq (insertDoubleAt x l0 a); intros;
    rewrite H1 in H0.
    eapply IHz.
    eapply insertDoubleAt_OddWindow.
    eauto.
    eauto.
    eauto.
    discriminate.

  Qed.

  Theorem combineOpt_OddWindow : forall l1 l2,
    Forall (fun a => match a with | Some x => ProgOddWindow x | None => True end) l1 ->
    combineOpt l1 = Some l2 ->
    Forall ProgOddWindow l2.

    induction l1; intros; simpl in *.
    inversion H0; clear H0; subst.
    econstructor.
    inversion H; clear H; subst.
    destruct a.
    case_eq (combineOpt l1); intros;
    rewrite H in H0.
    inversion H0; clear H0; subst.
    econstructor.
    trivial.
    eapply IHl1.
    trivial.
    trivial.
    discriminate.
    discriminate.
  Qed.

  Theorem multiSelect_OddWindow : forall l1 l2 l3,
    Forall ProgOddWindow l1 -> 
    multiSelect l1 l2 = Some l3 -> 
    Forall ProgOddWindow l3.

    intros.
    unfold multiSelect in *.
    eapply combineOpt_OddWindow; [idtac | eauto].
    eapply map_nth_error_Forall; eauto.

  Qed.

  Theorem signedWindowsToProg_ProgOddWindow_h : forall ws n,
    (n + length ws < numPrecompExponentGroups * precompTableSize)%nat -> 
    Forall OddWindow ws ->
    Forall ProgOddWindow (signedWindowsToProg ws n).

    induction ws; intros; simpl in *.
    econstructor.
    inversion H0; clear H0; subst.
    econstructor.
    unfold ProgOddWindow.
    intuition idtac.
    lia.
    eapply IHws.
    lia.
    trivial.

  Qed.

  Theorem signedWindowsToProg_ProgOddWindow : forall ws,
    (length ws < numPrecompExponentGroups * precompTableSize)%nat -> 
    Forall OddWindow ws ->
    Forall ProgOddWindow (signedWindowsToProg ws 0).

    intros.
    apply signedWindowsToProg_ProgOddWindow_h; eauto.

  Qed.

  Theorem permuteAndDouble_OddWindow : forall ws x y z l,
    (length ws < numPrecompExponentGroups * precompTableSize)%nat ->
    Forall OddWindow ws -> 
    permuteAndDouble ws x y z = Some l ->
    Forall ProgOddWindow l.

    intros.
    unfold permuteAndDouble in *.
    case_eq (multiSelect (signedWindowsToProg ws 0) y); intros;
    rewrite H2 in H1.
    eapply insertDoublesAt_OddWindow.
    eapply multiSelect_OddWindow.
    eapply signedWindowsToProg_ProgOddWindow; eauto.
    eauto.
    eauto.

    discriminate.

  Qed.
    
  Theorem groupedMul_precomp_equiv : forall d ws x x',
    (length ws < numPrecompExponentGroups * precompTableSize)%nat -> 
    Forall OddWindow ws -> 
    groupedMul_precomp d ws = Some x -> 
    groupedMul d ws = Some x' ->
    x == x'.

    intros.
    unfold groupedMul_precomp, groupedMul in *.
    optSomeInv.
    rewrite H3 in H4.
    inversion H4; clear H4; subst.
    symmetry.
    eapply groupMul_signedWindows_precomp_equiv.
    eapply permuteAndDouble_OddWindow;
    eauto.
    trivial.

  Qed.

  Theorem groupedMul_precomp_groupedMul_Some: forall d ws x,
    (length ws < numPrecompExponentGroups * precompTableSize)%nat -> 
    Forall OddWindow ws -> 
    groupedMul_precomp d ws = Some x -> 
    groupedMul d ws = None ->
    False.

    intros.
    unfold groupedMul_precomp, groupedMul in *.
    optSomeInv.
    rewrite H3 in H2.
    discriminate.

  Qed.

  Fixpoint groupMul_signedWindows_prog' e (ws : list WindowedMultOp) : GroupElem :=
    match ws with
    | nil => e
    | w :: ws' => evalWindowMult w (groupMul_signedWindows_prog' e ws')
    end.

  Fixpoint groupMul_signedWindows_prog_ls e (ws : list (list WindowedMultOp)) : GroupElem :=
    match ws with
    | nil => e
    | ls :: ws' => groupMul_signedWindows_prog' (groupMul_signedWindows_prog_ls e ws')  ls
    end.

  Theorem groupMul_signedWindows_prog'_app_equiv : forall ls1 ls2 e,
    groupMul_signedWindows_prog' e (ls1 ++ ls2) = groupMul_signedWindows_prog' (groupMul_signedWindows_prog' e ls2) ls1.

    induction ls1; intros; simpl in *.
    reflexivity.

    rewrite IHls1.
    reflexivity.

  Qed.

  Theorem groupMul_signedWindows_prog_ls_equiv : forall ls e,
    groupMul_signedWindows_prog_ls e ls = groupMul_signedWindows_prog' e (flatten ls).

    induction ls; intros; simpl in *.
    reflexivity.

    rewrite IHls.
    rewrite groupMul_signedWindows_prog'_app_equiv.
    reflexivity.

  Qed.

  Theorem groupMul_signedWindows_prog'_equiv : forall ls,
    groupMul_signedWindows_prog' idElem ls = groupMul_signedWindows_prog ls.

    induction ls; intros; simpl in *.
    reflexivity.
    rewrite IHls.
    reflexivity.

  Qed.

  (* When starting with the identity element, we can skip the first doubling *)
  Definition permuteAndDouble_grouped'  ws d perm :=
    if (eq_nat_dec (length perm) 0) then (Some nil) else
    let perm' := removelast perm in
    let x := last perm nil in
    match (multiSelect (signedWindowsToProg ws 0) x) with
    | None => None
    | Some y => 
      match (decrExpLs (length perm' * d) y) with
      | None => None
      | Some z =>   
        match (permuteAndDouble_grouped ws d perm') with
        | None => None
        | Some r => Some (r ++ (z :: nil))
        end
      end
    end.

  Theorem groupMul_signedWindows_prog'_compat:
    forall ls e1 e2,
      e1 == e2 -> 
      groupMul_signedWindows_prog' e1 ls == groupMul_signedWindows_prog' e2 ls.

    induction ls; intros; simpl in *.
    trivial.
    eapply evalWindowMult_compat; eauto.

  Qed.

  Theorem permuteAndDouble_grouped_no_double_equiv : forall ws d perm x,
    permuteAndDouble_grouped ws d perm = Some x ->
    exists x', permuteAndDouble_grouped' ws d perm = Some x' /\
    groupMul_signedWindows_prog_ls idElem x ==  groupMul_signedWindows_prog_ls idElem x'.

    intros.
    unfold permuteAndDouble_grouped in *. 
    optSomeInv.
    destruct perm using rev_ind; simpl in *.
    optSomeInv.
    simpl in *.
    optSomeInv.
    exists nil.
    intuition idtac.  
    simpl in *.
    reflexivity.

    clear IHperm.
    rewrite map_app in *.
    rewrite combineOpt_app in *.
    optSomeInv.
    simpl in *.
    optSomeInv.
    apply decrExpsLs_app in H1.
    destruct H1.
    destruct H1.
    destruct H1.
    intuition idtac; subst.
    simpl in *.
    optSomeInv.
    simpl in *.
    optSomeInv.

    unfold permuteAndDouble_grouped'.
    rewrite app_length.
    simpl.
    destruct (Nat.eq_dec (length perm + 1) 0).
    lia.
    rewrite last_last.
    rewrite removelast_last.
    rewrite H0.
    unfold permuteAndDouble_grouped.
    rewrite H.
    rewrite H2.
    replace (length perm) with (length l1).
    rewrite H1.
    econstructor.
    intuition idtac.
    rewrite map_app.
    simpl.
    repeat rewrite groupMul_signedWindows_prog_ls_equiv.
    repeat rewrite flatten_app.
    repeat rewrite groupMul_signedWindows_prog'_app_equiv.
    simpl.
    repeat rewrite groupMul_signedWindows_prog'_app_equiv.
    simpl.
    eapply groupMul_signedWindows_prog'_compat.
    eapply groupMul_signedWindows_prog'_compat.
    eapply groupDouble_n_id; eauto.
    apply combineOpt_length in H.
    rewrite map_length in *.
    lia.

  Qed.

End GeneratorMul.


