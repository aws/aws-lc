(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0 *)

Set Implicit Arguments.

(* A machine that can calculate a group multiplication by performing somewhat arbitrary double and add operations.
We can perform transformations on the machine and show that the result of the calculation is unchanged. This gives
us a simple way to describe various optimized group multiplication operations. We can start with a program that is
equivalent to some windowed multiplication operation that was proved correct in GroupMulWNAF. Then we transform 
the program until it is equivalent to some other operation (e.g. an optimized implementation in code). The transformation
operations may fail, so it is also necessary to prove that the desired transformations will succeed. *)

Require Import ZArith.BinInt.
Require Import List.
Require Import Arith.
Require Import Arith.Peano_dec.
Require Import Arith.Compare_dec.
Require Import Permutation.
Require Import Nat.
Require Import micromega.Lia.
Require Import SetoidClass.

From EC Require Import GroupMulWNAF.


Inductive WindowedMultOp :=
  | wm_Add : nat -> Z -> WindowedMultOp (* Add (z * 2^n) * g to the accumulator, where g is a group element *)  
  | wm_Double : nat -> WindowedMultOp (* Double the value in the accumulator *)
.

(* Take a list of signed windows and convert them to a program *)
Fixpoint signedWindowsToProg (ws : list SignedWindow)(n : nat) :=
  match ws with
  | nil => nil
  | w :: ws' => (wm_Add n w) :: (signedWindowsToProg ws' (S n))
  end.

Theorem nth_error_signedWindowsToProg_Some : forall ls x n1 n2 n3,
  nth_error (signedWindowsToProg ls n1) n2 = Some (wm_Add n3 x) ->
  nth_error ls n2 = Some x.

  induction ls; destruct n2; intros; simpl in *; try discriminate.
  inversion H; clear H; subst.
  reflexivity.
  eapply IHls; eauto.

Qed.

Theorem nth_error_signedWindowsToProg_Some_add : forall ls x n1 n2,
  nth_error (signedWindowsToProg ls n1) n2 = Some x ->
  exists y, nth_error ls n2 = Some y /\ x =  (wm_Add (n1 + n2) y).

  induction ls; destruct n2; intros; simpl in *; try discriminate.
  inversion H; clear H; subst.
  rewrite Nat.add_0_r.
  econstructor; intuition idtac.
  edestruct IHls; eauto.
  intuition idtac; subst.
  exists x0.
  intuition idtac.
  f_equal.
  lia.

Qed.

(* Operations that preserve the value *)

(* Insert a double at the head of the list and adjust exponents on remaining items. This operation factors the
doubling out of the remaining list, and it will only succeed in circumstances where each element in the list has
the required factors. For example, if we want to double 5 times at the beginning of the list, this will succeed 
if an only if the list looks like [x1 * 2^(y1 + 5), x2 * 2^(y2 + 5), ... , xn * 2^(yn + 5)]. In other words, it will 
succeed if and only if each exponent is at least 5. *)
Definition decrExp (n : nat)(p : WindowedMultOp) :=
  match p with
  | wm_Add n' w =>
    if (le_dec n n') then (Some (wm_Add (n' - n) w)) else None
  | wm_Double n' => Some (wm_Double n')
  end.

Fixpoint decrExpLs (n : nat)(ps : list WindowedMultOp) :=
  match ps with
  | nil => Some nil
  | p :: ps' =>
    match (decrExp n p) with
    | None => None
    | Some p' => 
      match (decrExpLs n ps') with
      | None => None
      | Some ps'' =>
        Some (p' :: ps'')
      end
    end
  end.

Definition insertDouble n ps :=
  match (decrExpLs n ps) with
  | Some ps' => Some ((wm_Double n) :: ps')
  | None => None
  end.

Fixpoint insertDoubleAt d (ls : list WindowedMultOp)(n : nat) : option (list WindowedMultOp) :=
  match n with
  | O => (insertDouble d ls)
  | S n' => 
    match ls with
    | nil => None
    | x :: ls' =>
      match (insertDoubleAt d ls' n') with
      | None => None
      | Some ls'' => Some (x :: ls'')
      end
    end
  end.

Fixpoint insertDoublesAt d ls lsn :=
  match lsn with
  | nil => Some ls
  | n :: lsn' => 
    match (insertDoubleAt d ls n) with
    | None => None
    | Some ls' => insertDoublesAt d ls' lsn'
    end
  end.

(* We can arbitrarily permute and insert accumulator doublings. If it succeeds, then the value computed 
by this program will be the same as the basic windowed multiplication. *)
Definition permuteAndDouble ws d (perm doubles : list nat) :=
  match (multiSelect (signedWindowsToProg ws 0) perm) with
  | None => None
  | Some ps => insertDoublesAt d ps doubles
  end.


Fixpoint decrExpsLs n ps :=
  match ps with
  | nil => Some nil
  | p :: ps' => 
    match (decrExpsLs n ps') with
    | None => None
    | Some x => 
      match (combineOpt (map (decrExpLs  n) x)) with
      | None => None
      | Some x' => Some (p :: x')
      end
    end
  end.

Theorem decrExpsLs_length : forall d x y,
  decrExpsLs d x = Some y ->
  Datatypes.length x = Datatypes.length y.

  induction x; intros; simpl in *.
  inversion H; clear H; subst.
  reflexivity.
  case_eq (decrExpsLs d x); intros;
  rewrite H0 in H.
  case_eq (combineOpt (List.map (decrExpLs d) l)); intros;
  rewrite H1 in H.
  inversion H; clear H; subst.
  simpl.
  f_equal.
  apply combineOpt_length in H1.
  rewrite map_length in *.
  rewrite <- H1.
  eapply IHx; eauto.
  discriminate.
  discriminate.

Qed.

(* A specialization of permuteAndDouble that only inserts doublings after each grouping *)
Definition permuteAndDouble_grouped ws d (perm : list (list nat)) :=
  match (combineOpt (map (multiSelect (signedWindowsToProg ws 0)) perm)) with
  | None => None
  | Some ps => 
    match (decrExpsLs d ps) with
    | None => None
    | Some x => Some (map (fun x=> x ++ (wm_Double d)::nil ) x)
    end
  end.

(* Swap the order of two operations *)
Definition swapPair p1 p2 :=
  match p1 with
  | wm_Add n1 z1 =>
    match p2 with
    | wm_Add n2 z2 => Some (p2, p1)
    | wm_Double n2 => 
      if (le_dec n2 n1) then Some (p2, (wm_Add (n1 - n2) z1)) else None
    end
  | wm_Double n1 =>
    match p2 with
    | wm_Add n2 z2 => Some ((wm_Add (n1 + n2) z2),  p1)
    | wm_Double n2 => Some (p2, p1)
    end
  end.

Definition swapFront ps := 
  match ps with 
  | nil => None
  | p1 :: ps' =>
    match ps' with
    | nil => None
    | p2 :: ps'' =>
      match (swapPair p1 p2) with
      | None => None
      | Some (a, b) => Some (a :: b ::  ps'')
      end
    end
  end.

(* A predicate stating that a program contains only add operations *)
Definition AddProg : list WindowedMultOp -> Prop :=
  Forall (fun x => match x with | wm_Add _ _ => True | _ => False end).

Definition divides x y :=
  eq_nat_dec (gcd x y) x.


(* returns true if v = k*x + y for some k, false otherwise*)
Definition isMultiple v x y :=
  if (ge_dec v y) then (if (divides x (v - y)) then true else false) else false.

Fixpoint endIndices_h(A : Type)(ls : list (list A))(x : nat) :=
    match ls with
    | nil => nil
    | a :: ls' => 
      ((length a) + x)%nat :: (endIndices_h ls' (length a + x))
    end.

(* insert doublings from back to front so that it doesn't upset earlier indices *)
Definition endIndices(A : Type)(ls : list (list A)) :=
  (rev (endIndices_h ls O)).

Theorem isMultiple_true : forall a x b,
  isMultiple (a * x + b) x b = true.

  intros.
  unfold isMultiple.
  destruct (ge_dec (a * x + b) b).
  rewrite Nat.add_sub.
  unfold divides.
  replace (a * x)%nat with (0 + a * x)%nat.
  rewrite Nat.gcd_add_mult_diag_r.
  rewrite Nat.gcd_0_r.
  destruct (Nat.eq_dec x x).
  trivial.
  intuition idtac.
  lia.
  lia.

Qed.


Theorem isMultiple_true_if : forall y x b,
  isMultiple y x b = true ->
  exists a, y  = (a * x + b)%nat.

  intros. 
  unfold isMultiple in *.
  destruct (ge_dec y b).
  destruct (eq_nat_dec x O).
  subst.
  exists O.
  simpl.
  unfold divides in *.
  destruct (Nat.eq_dec (gcd O (y - b))%nat).
  apply Nat.gcd_eq_0_r in e.
  lia.
  discriminate.
  exists ((y - b) / x)%nat.
  unfold divides in *.
  destruct (Nat.eq_dec (gcd x (y - b)) x).
  replace ((y - b) / x * x )%nat with ((y - b) / Nat.gcd (y - b) x * x)%nat.
  rewrite Nat.lcm_equiv2.
  rewrite Nat.gcd_comm.
  rewrite e.
  rewrite Nat.div_mul.
  lia.
  trivial.
  intuition idtac.
  rewrite Nat.gcd_comm in H0.
  rewrite H0 in e.
  lia.
  rewrite Nat.gcd_comm.
  rewrite e.
  reflexivity.  
  discriminate.
  discriminate.
Qed.

Fixpoint lsMultiples(nMax numGroups curGroup : nat) :=
  match nMax with
  | O => nil
  | S nMax' => (lsMultiples nMax' numGroups curGroup) ++ 
  (if (isMultiple nMax' numGroups curGroup) then nMax'::nil else nil)
   
end.

Theorem In_lsMultiples : forall nMax a x b,
  (b < x)%nat ->
  (a * x + b < nMax)%nat -> 
  In (a * x + b)%nat (lsMultiples nMax x b).

  induction nMax; intros; simpl in *.
  lia.
  destruct (eq_nat_dec (a*x + b) nMax).
  subst.
  apply in_or_app.
  right.
  rewrite isMultiple_true.
  simpl.
  intuition idtac.
  apply in_or_app.
  left.
  eapply IHnMax.
  eauto.
  lia.

Qed.

Theorem In_lsMultiples_if : forall nMax a x b,
  In a (lsMultiples nMax x b) -> 
  (a < nMax)%nat.

  induction nMax; intros; simpl in *.
  intuition idtac.
  destruct (isMultiple nMax x b); intros.
  apply in_app_or in H.
  simpl in *.
  intuition idtac.
  eapply IHnMax in H0.
  lia.
  subst.
  lia.   
  rewrite app_nil_r in *.
  apply IHnMax in H.
  lia.

Qed.

Theorem lsMultiples_gcd : forall nw m i, 
  List.Forall (fun x : nat => Nat.gcd (x - i) m = m) (lsMultiples nw m i).

  induction nw; intros; simpl in *.
  econstructor.
  eapply Forall_app.
  intuition idtac.
  eauto.
  case_eq (isMultiple nw m i ); intros.
  econstructor.
  unfold isMultiple in *.
  destruct ( ge_dec nw i). 
  unfold divides in *.  
  destruct (Nat.eq_dec (gcd m (nw - i)) m).
  rewrite Nat.gcd_comm.
  eauto.
  discriminate.
  discriminate.
  econstructor.
  econstructor.

Qed.

Theorem lsMultiples_div : forall nw m i, 
  i < m ->
  m > 0 ->
  List.Forall (fun x : nat => Nat.div x m = Nat.div (x - i) m) (lsMultiples nw m i).

  induction nw; intros; simpl in *.
  econstructor.
  eapply Forall_app.
  intuition idtac.
  eauto.
  case_eq (isMultiple nw m i ); intros.
  econstructor.
  unfold isMultiple in *.
  destruct (ge_dec nw i ).
  destruct (divides m (nw - i)); intros.
  assert (exists y, nw = i + y).
  exists (nw - i).
  lia.
  destruct H2.
  subst.
  replace (i + x - i) with x in *.   
  assert (exists y, x = y * m).
  exists (Nat.div x m).
  rewrite <- e at 1.
  rewrite Nat.mul_comm.
  rewrite <- Nat.gcd_div_swap.
  rewrite e.
  rewrite Nat.mul_comm.
  rewrite Nat.div_same.
  lia.
  lia.
  destruct H2.
  subst.
  rewrite Nat.div_add.
  rewrite Nat.div_small.
  rewrite Nat.div_mul.
  lia.
  lia.
  lia.
  lia.
  lia.
  discriminate.
  discriminate.
  econstructor.
  econstructor.

Qed.

Theorem lsMultiples_length_weak : forall nw m i,
  List.Forall (fun x : nat => x < nw) (lsMultiples nw m i).

  induction nw; intros; simpl in *.
  econstructor.
  eapply Forall_app.
  intuition idtac.
  eapply Forall_impl; eauto.
  intuition idtac; lia.
  case_eq (isMultiple nw m i); intros.
  unfold isMultiple in *.
  destruct (ge_dec nw i).
  econstructor.
  lia.
  econstructor.
  discriminate.
  econstructor.
  
Qed.


Fixpoint groupIndices_h(nMax numGroups curGroup : nat) :=
  match curGroup with
  | O => nil
  | S curGroup' => 
    (groupIndices_h nMax numGroups curGroup') ++ ((lsMultiples nMax numGroups curGroup') :: nil)
  end.

Definition groupIndices nMax numGroups :=
  groupIndices_h nMax numGroups numGroups.

Theorem In_groupIndices_h : forall  b1 b2 a x nMax,
  (b2 < b1)%nat -> 
  (b2 < x)%nat ->
  (a * x + b2 < nMax)%nat -> 
  In (a * x + b2)%nat  (flatten (groupIndices_h nMax x b1)).

  induction b1; intros; simpl in *.
  lia.
  
  destruct (eq_nat_dec b2 b1).
  subst.
  rewrite flatten_app.
  apply in_or_app.
  simpl.
  right.
  apply in_or_app.
  left.
  eapply In_lsMultiples.
  trivial.
  trivial.
  rewrite flatten_app.
  apply in_or_app.
  left.
  eapply IHb1.
  lia.
  trivial.
  trivial.
Qed.

Theorem In_groupIndices_h_if : forall  b1 a x nMax,
  In a (flatten (groupIndices_h nMax x b1)) -> 
  (a < nMax)%nat.

  induction b1; intros; simpl in *.
  intuition idtac.
  rewrite flatten_app in *.
  simpl in *.
  rewrite app_nil_r in *.
  assert (In a (flatten (groupIndices_h nMax x b1)) \/ In a (lsMultiples nMax x b1)).
  eapply in_app_or.
  eapply H.
  intuition idtac.
  eapply IHb1; eauto.
  eapply In_lsMultiples_if; eauto.

Qed.

Theorem lsMultiples_NoDup : forall nMax x a,
  NoDup (lsMultiples nMax x a).

  induction nMax; intros; simpl in *.
  econstructor.
  eapply NoDup_app.
  eauto.
  destruct (isMultiple nMax x a).
  econstructor.
  simpl.
  intuition idtac.
  econstructor.
  econstructor.
  intros.
  apply In_lsMultiples_if in H.
  destruct (isMultiple nMax x a); simpl in *.
  intuition idtac; subst.
  lia.
  intuition idtac.

Qed.

Theorem in_lsMultiples_isMultiple : forall n x a b,
  In x (lsMultiples n a b) ->
  exists y, (x = y * a + b)%nat.

  induction n; intros; simpl in *.
  intuition idtac.
  apply in_app_or in H.
  intuition idtac.
  eauto.
  case_eq (isMultiple n a b); intros;
  rewrite H in H0.
  simpl in *.
  intuition idtac; subst.
  apply isMultiple_true_if.
  trivial.
  simpl in *; intuition idtac.

Qed.

Theorem in_groupIndices_h_isMultiple : forall b a x nMax,
  In a (flatten (groupIndices_h nMax x b)) ->
  exists y b', (b' < b /\ a = y * x + b')%nat.

  induction b; intros; simpl in *.
  intuition idtac.
  rewrite flatten_app in *.
  simpl in *.
  rewrite app_nil_r in *.
  apply in_app_or in H.
  intuition idtac.
  edestruct IHb.
  eauto.
  destruct H.
  intuition idtac.
  subst.
  econstructor.
  exists x1.
  intuition idtac.
  lia.
  apply in_lsMultiples_isMultiple in H0.
  destruct H0.
  subst.
  econstructor.
  exists b.
  intuition idtac.
  lia.

Qed.

Theorem groupIndices_h_NoDup : forall  b x nMax,
  (b <= x)%nat -> 
  NoDup (flatten (groupIndices_h nMax x b)).

  induction b; intros; simpl in *.
  econstructor.
  rewrite flatten_app.
  simpl.
  rewrite app_nil_r.
  eapply NoDup_app.
  eapply IHb.
  lia.
  apply lsMultiples_NoDup.

  intros.
  apply in_lsMultiples_isMultiple in H1.
  apply in_groupIndices_h_isMultiple in H0.
  destruct H0.
  destruct H0.
  destruct H1.
  intuition idtac.
  subst.
  eapply mul_add_mod_ne; [idtac | idtac | eauto].
  lia.
  lia.

Qed.


Theorem groupIndices_perm : forall x y,
  y <> O -> 
  Permutation (seq 0 x) (flatten (groupIndices x y)).

  intros.
  eapply NoDup_Permutation.
  apply seq_NoDup.
  apply groupIndices_h_NoDup.
  lia.

  intros.
  intuition idtac.
  rewrite (Nat.div_mod_eq x0 y).
  rewrite Nat.mul_comm.
  unfold groupIndices.
  eapply In_groupIndices_h.
  apply Nat.mod_upper_bound.
  intuition idtac.
  apply Nat.mod_upper_bound.
  intuition idtac.
  rewrite Nat.mul_comm.
  rewrite <- (Nat.div_mod_eq x0 y).
  apply in_seq in H0.
  lia.

  apply in_seq.
  apply In_groupIndices_h_if in H0.
  lia.

Qed.

Theorem decrExp_0 : forall x,
  decrExp 0 x = Some x.

  intros.
  unfold decrExp.
  destruct x.
  destruct (Compare_dec.le_dec 0 n).
  rewrite Nat.sub_0_r.
  reflexivity.
  lia.
  reflexivity.

Qed.

Theorem decrExpLs_0 : forall x,
  decrExpLs 0 x = Some x.

  induction x; intros; simpl in *.
  reflexivity.
  rewrite decrExp_0.
  rewrite IHx.
  reflexivity.

Qed.

Theorem decrExp_plus : forall x y a b,
  decrExp a x = Some y -> 
  decrExp (a + b) x = decrExp b y.

  intros.
  unfold decrExp in *.
  destruct x.
  destruct (le_dec a n ).
  inversion H; clear H; subst.
  destruct (le_dec (a + b) n).  
  destruct (Compare_dec.le_dec b (n - a) ).
  f_equal.
  f_equal.
  lia.
  lia.
  destruct (Compare_dec.le_dec b (n - a)).
  lia.
  reflexivity.
  discriminate.
  inversion H; clear H; subst.
  reflexivity.

Qed.

Theorem decrExpLs_plus : forall x y a b,
  decrExpLs a x = Some y -> 
  decrExpLs (a + b) x = decrExpLs b y.

  induction x; intros; simpl in *.
  inversion H; clear H; subst.
  reflexivity.

  optSomeInv.
  simpl in *.
  erewrite IHx; eauto.
  erewrite decrExp_plus.
  reflexivity.
  eauto.
Qed.

Theorem decrExpsLs_app : forall d ls1 ls2 x,
  decrExpsLs d (ls1 ++ ls2) = Some x ->
  exists x1 x2 x3,
    decrExpsLs d ls1 = Some x1 /\
    decrExpsLs d ls2 = Some x2 /\
    combineOpt (List.map (decrExpLs ((List.length ls1) * d)) x2) = Some x3 /\
    x = x1 ++ x3.

  induction ls1; intros; simpl in *.
  econstructor.
  econstructor.
  econstructor.
  intuition idtac.
  eauto.
  erewrite (List.map_ext _ (fun x => Some x)).
  eapply combineOpt_id.
  eapply decrExpLs_0.

  case_eq (decrExpsLs d (ls1 ++ ls2)); intros;
  rewrite H0 in H.
  case_eq (combineOpt (List.map (decrExpLs d) l) ); intros;
  rewrite H1 in H.
  inversion H; clear H; subst.
  edestruct IHls1; eauto.
  destruct H.
  destruct H.
  intuition idtac; subst.
  rewrite H2.
  rewrite map_app in *.
  rewrite combineOpt_app in *.
  case_eq (combineOpt (List.map (decrExpLs d) x) ); intros;
  rewrite H4 in H1.
  case_eq (combineOpt (List.map (decrExpLs d) x1)); intros;
  rewrite H5 in H1.
  inversion H1; clear H1; subst.
  econstructor.
  econstructor.
  econstructor.
  intuition idtac.
  eauto.

  erewrite combineOpt_map_map; [
  reflexivity | idtac | eauto | eauto].
  intros.
  rewrite Coq.Arith.Plus.plus_comm.
  eapply decrExpLs_plus.
  eauto.

  discriminate.
  discriminate.
  discriminate.
  discriminate.

Qed.

Theorem permuteAndDouble_grouped_length : forall ls rwnaf n x,
  permuteAndDouble_grouped rwnaf n ls = Some x -> 
  List.length x = List.length ls.

  intros.
  unfold permuteAndDouble_grouped in *.
  optSomeInv.
  rewrite map_length.
  eapply combineOpt_length in H0.
  rewrite map_length in *.
  rewrite H0.
  
  symmetry.
  eapply decrExpsLs_length.
  eauto.

Qed.

Theorem groupIndices_h_length : forall nw n x,
  List.length (groupIndices_h nw x n) = n.

  induction n; intros; simpl in *.
  reflexivity.
  rewrite app_length.
  simpl.
  rewrite IHn.
  lia.

Qed.

Theorem groupIndices_length : forall n x,
  List.length (groupIndices n x) = x.

  intros.
  unfold groupIndices.
  apply groupIndices_h_length.
Qed.

Theorem signedWindowsToProg_length : forall ws n,
  length (signedWindowsToProg ws n) = length ws.

  induction ws; intros; simpl in *. 
  reflexivity.
  f_equal.
  eauto.

Qed.

Theorem signedWindowsToProg_AddProg : forall ws n,
  AddProg (signedWindowsToProg ws n).

  induction ws; intros; unfold AddProg in *; simpl in *.
  econstructor.
  econstructor.
  trivial.
  eapply IHws.

Qed.

Theorem decrExpLs_app : forall ls1 ls2 d ls1' ls2',
  decrExpLs d ls1 = Some ls1' ->
  decrExpLs d ls2 = Some ls2' ->
  decrExpLs d (ls1 ++ ls2) = Some (ls1' ++ ls2').

  induction ls1; intros; simpl in *.
  inversion H; clear H; subst.
  simpl in *.
  trivial.
  case_eq (decrExpLs d ls1); intros.
  rewrite H1 in H.
  case_eq (decrExp d a); intros.
  rewrite H2 in H.
  inversion H; clear H; subst.
  erewrite IHls1.
  reflexivity.
  trivial.
  trivial.
  rewrite H2 in H.
  discriminate.
  rewrite H1 in H.
  destruct (decrExp d a).
  discriminate.
  discriminate.

Qed.

Theorem permuteAndDouble_grouped_cons : forall a perm ws d ls,
  permuteAndDouble_grouped ws d (a :: perm) = Some ls ->
  exists ls1 a1 ls2 , permuteAndDouble_grouped ws d perm = Some ls1 /\
  multiSelect (signedWindowsToProg ws 0) a = Some a1 /\
  combineOpt (map (decrExpLs d) ls1) = Some ls2 /\
  ls = (a1 ++ (wm_Double d):: nil)  :: ls2.
  
  intros.
  unfold permuteAndDouble_grouped in *.
  simpl in *.
  case_eq (multiSelect (signedWindowsToProg ws 0) a ); intros.
  rewrite H0 in H.
  case_eq (combineOpt (map (multiSelect (signedWindowsToProg ws 0)) perm)); intros.
  rewrite H1 in H.
  simpl in *.
  case_eq (decrExpsLs d l0); intros.
  rewrite H2 in H.
  
  case_eq (combineOpt (map (decrExpLs d) l1)); intros.
  rewrite H3 in H.
  inversion H; clear H; subst.
  exists (map
 (fun x : list WindowedMultOp => x ++ wm_Double d :: nil)
 l1) .
  exists l.
  exists (map
    (fun x : list WindowedMultOp =>
     x ++ wm_Double d:: nil) l2).
  intuition idtac.
  rewrite <- (combineOpt_map (fun x : list WindowedMultOp => x ++ wm_Double d :: nil) (map (decrExpLs d) l1)); trivial.
  f_equal.
  repeat rewrite map_map.
  eapply map_ext_in_iff.
  intros.
  case_eq (decrExpLs d a0); intros. 
  erewrite decrExpLs_app; simpl; eauto.
  exfalso.
  eapply combineOpt_In_not_None;[eapply H3 | idtac | eapply H4].
  eapply in_map_iff.
  econstructor.
  intuition idtac.

  rewrite H3 in H.
  discriminate.
  rewrite H2 in H.
  discriminate.
  rewrite H1 in H.
  discriminate.
  rewrite H0 in H.
  discriminate.
Qed.

Theorem decrExpLs_app_if : forall d x y z,
  decrExpLs d (x ++ y) = Some z ->
  exists a b, decrExpLs d x = Some a /\ decrExpLs d y = Some b /\ z = a ++ b.

  induction x; intros; simpl in *.
  exists nil, z.
  intuition idtac.
  case_eq (decrExp d a); intros;
  rewrite H0 in H.
  case_eq (decrExpLs d (x++y)); intros;
  rewrite H1 in H.
  inversion H; clear H; subst.
  edestruct IHx; eauto.
  destruct H.
  intuition idtac; subst.
  rewrite H2.
  econstructor; econstructor; intuition eauto.
  discriminate.
  discriminate.

Qed.

Theorem permuteAndDouble_grouped_cons_if : forall a perm ws d ls1 a1 ls2,
  permuteAndDouble_grouped ws d perm = Some ls1 ->
  multiSelect (signedWindowsToProg ws 0) a = Some a1 ->
  combineOpt (map (decrExpLs d) ls1) = Some ls2 ->
  permuteAndDouble_grouped ws d (a :: perm) = Some ((a1 ++ (wm_Double d):: nil)  :: ls2).

  intros.
  unfold permuteAndDouble_grouped in *.
  simpl.
  rewrite H0.
  case_eq (combineOpt (map (multiSelect (signedWindowsToProg ws 0)) perm)); intros;
  rewrite H2 in H.
  simpl.
  case_eq (decrExpsLs d l); intros;
  rewrite H3 in H.
  inversion H; clear H; subst.
  apply combineOpt_map_comm in H1.
  destruct H1.
  intuition idtac.
  subst.
  rewrite H1.
  simpl.
  reflexivity.

  intros.
  edestruct decrExpLs_app_if; eauto.
  destruct H4.
  intuition idtac; subst.
  inversion H4; clear H4; subst.
  econstructor.
  intuition idtac; eauto.
  discriminate.
  discriminate.
Qed.

Theorem insertDoubleAt_0 : forall d l1,
  insertDoubleAt d l1 0 = insertDouble d l1.

  induction l1; intros; simpl in *;
  reflexivity.

Qed.

Theorem insertDoubleAt_app : forall l0 l1 d x,
  insertDoubleAt d (l0 ++ l1) (length l0)  = Some x ->
  exists y, decrExpLs d l1 = Some y /\
  x = (l0 ++ (wm_Double d):: y).

  induction l0; intros; simpl in *.
  rewrite insertDoubleAt_0 in H.
  unfold insertDouble in *.
  case_eq (decrExpLs d l1); intros.
  rewrite H0 in H.
  inversion H; clear H; subst.
  econstructor; eauto.
  rewrite H0 in H.
  discriminate.
  case_eq (insertDoubleAt d (l0 ++ l1) (length l0) ); intros;
  rewrite H0 in H.
  inversion H; clear H; subst.
  edestruct IHl0; eauto.
  intuition idtac.
  subst.
  exists x.
  intuition idtac.
  discriminate.

Qed.

Theorem insertDoubleAt_ge : forall a l0 l1 d l,
  (a >= length l0)%nat ->
  insertDoubleAt d (l0 ++ l1) a = Some l ->
  exists b l2, insertDoubleAt d l1 b = Some l2 /\
  l = l0 ++ l2 /\ (a = (length l0) + b)%nat.

  induction a; intros; simpl in *.
  rewrite insertDoubleAt_0 in *.
  replace l0 with (@nil WindowedMultOp) in *.
  simpl in *.
  exists 0%nat.
  exists l.
  rewrite insertDoubleAt_0 in *.
  intuition idtac.
  destruct l0; simpl in *; trivial.
  lia.

  destruct l0; simpl in *.
  exists (S a).
  exists l.
  intuition idtac.
  case_eq (insertDoubleAt d (l0 ++ l1) a); intros;
  rewrite H1 in H0.
  inversion H0; clear H0; subst.
  edestruct (IHa l0).
  lia.
  eauto.
  destruct H0.
  intuition idtac; subst.
  exists x.
  exists x0.
  intuition idtac.
  discriminate.

Qed.


Theorem insertDoubleAt_app_if : forall l0 l1 d x0 x,
  insertDoubleAt d l1 x0 = Some x -> 
  insertDoubleAt d (l0 ++ l1) (length l0 + x0) = Some (l0 ++ x).

  induction l0; intros; simpl in *.
  trivial.
  erewrite IHl0.
  reflexivity.
  trivial.

Qed.


Theorem insertDoublesAt_app : forall lsn d l0 l1 x,
  (forall n, In n lsn -> n >= length l0)%nat ->
  insertDoublesAt d (l0 ++ l1) (lsn ++ length l0 :: nil)  = Some x -> 
  exists y z, 
  (insertDoublesAt d l1 (map (fun x => minus x (length l0)) lsn)) = Some y /\
  decrExpLs d y = Some z /\
  x = l0 ++ (wm_Double d)::z.

  induction lsn; intros; simpl in *.
  case_eq (insertDoubleAt d (l0 ++ l1) (length l0)); intros.
  rewrite H1 in H0.
  inversion H0; clear H0; subst.
  edestruct insertDoubleAt_app; eauto.
  rewrite H1 in H0.
  discriminate.

  case_eq (insertDoubleAt d (l0 ++ l1) a); intros.
  rewrite H1 in H0.
  apply insertDoubleAt_ge in H1.
  destruct H1.
  destruct H1.
  intuition idtac; subst.
  edestruct (IHlsn d l0).
  intuition idtac.
  eapply H.
  intuition idtac.
  eauto.
  destruct H1.
  intuition idtac; subst.
  rewrite minus_plus.
  rewrite H2.
 
  exists x2.
  exists x3.
  intuition idtac.
  eapply H.
  intuition idtac.
  
  rewrite H1 in H0.
  discriminate.

Qed.

Theorem insertDoublesAt_app_if : forall lsn d l0 l1 y z,
  (forall n, In n lsn -> n >= length l0)%nat ->
  (insertDoublesAt d l1 (map (fun x => minus x (length l0)) lsn)) = Some y ->
  decrExpLs d y = Some z ->
   insertDoublesAt d (l0 ++ l1) (lsn ++ length l0 :: nil)  = Some (l0 ++ (wm_Double d)::z).

  induction lsn; intros; simpl in *.
  inversion H0; clear H0; subst.
  replace (length l0) with (length l0 + 0)%nat.
  erewrite insertDoubleAt_app_if.
  reflexivity.
  rewrite insertDoubleAt_0.
  unfold insertDouble.
  rewrite H1.
  reflexivity.
  lia.
  
  case_eq (insertDoubleAt d l1 (a - length l0) ); intros;
  rewrite H2 in H0.
  replace a with (length l0 + (a - length l0))%nat.
  erewrite insertDoubleAt_app_if.
  eapply IHlsn.
  intros.
  eapply H.
  intuition idtac.
  eauto.
  trivial.
  trivial.
  specialize (H a).
  intuition idtac.
  lia.
  discriminate.

Qed.

Theorem endIndices_h_map_sub : forall (A : Type)(ls : list (list A)) x y,
  (y <= x)%nat ->
  map (fun n => minus n y) (endIndices_h ls x) = endIndices_h ls (minus x y).

  induction ls; intros; simpl in *.
  reflexivity.
  f_equal.
  lia.
  rewrite IHls.
  f_equal.
  lia.
  lia.

Qed.

Theorem In_endIndices_h_ge : forall (A : Type)(ls : list (list A)) n m,
  In n (endIndices_h ls m) ->
  (n >= m)%nat.

  induction ls; intros; simpl in *.
  intuition idtac.
  intuition idtac; subst.
  lia.
  eapply le_trans; [idtac |
  eapply IHls; eauto].
  lia.

Qed.

Theorem permuteAndDouble_flatten_app_cons : forall  ws d a perm x,
  permuteAndDouble ws d (a ++ flatten perm) (endIndices (a :: perm))  = Some x ->
  exists a1 x1 x2, multiSelect (signedWindowsToProg ws 0) a = Some a1 /\
  permuteAndDouble ws d (flatten perm) (endIndices perm) = Some x1 /\
  decrExpLs d x1 = Some x2 /\
  x = a1 ++ (wm_Double d)::x2.

  intros.
  unfold permuteAndDouble in *.
  case_eq (multiSelect (signedWindowsToProg ws 0) (a ++ flatten perm)); intros.
  rewrite H0 in H.
  rewrite multiSelect_app in *.
  case_eq (multiSelect (signedWindowsToProg ws 0) a); intros.
  rewrite H1 in H0.
  exists l0.
  case_eq (multiSelect (signedWindowsToProg ws 0) (flatten perm) ); intros.
  rewrite H2 in H0.
  inversion H0; clear H0; subst.
  unfold endIndices in *.
  simpl in *.
  rewrite plus_0_r in *.
  replace (length a) with (length l0) in H.
  apply insertDoublesAt_app in H.
  destruct H.
  destruct H.
  intuition idtac. subst.
  rewrite map_rev in *.
  rewrite endIndices_h_map_sub in *.
  rewrite minus_diag in *.
  exists x0.
  exists x1.
  intuition idtac.
  lia.

  intros.
  apply in_rev in H0.
  eapply In_endIndices_h_ge; eauto.
  symmetry.
  eapply multiSelect_length; eauto.
  rewrite H2 in H0.
  discriminate.
  rewrite H1 in H0.
  discriminate.
  rewrite H0 in H.
  discriminate.

Qed.

Theorem permuteAndDouble_flatten_app_cons_if : forall  ws d a perm a1 x1 x2,
  multiSelect (signedWindowsToProg ws 0) a = Some a1 ->
  permuteAndDouble ws d (flatten perm) (endIndices perm) = Some x1 -> 
  decrExpLs d x1 = Some x2 -> 
  permuteAndDouble ws d (a ++ flatten perm) (endIndices (a :: perm))  = Some (a1 ++ (wm_Double d)::x2).

  intros.
  unfold permuteAndDouble in *.
  case_eq (multiSelect (signedWindowsToProg ws 0) (flatten perm) ); intros.
  rewrite H2 in H0.
  rewrite multiSelect_app.
  rewrite H2.
  rewrite H.
  unfold endIndices. simpl.
  rewrite plus_0_r.
  replace (length a) with (length a1).
  erewrite insertDoublesAt_app_if.
  reflexivity.
  intros.
  eapply In_endIndices_h_ge.
  eapply in_rev.
  eauto.
  rewrite map_rev.
  erewrite endIndices_h_map_sub.
  rewrite minus_diag.
  eapply H0.
  lia.
  trivial.
  symmetry.
  eapply multiSelect_length.
  eauto.
  rewrite H2 in H0.
  discriminate.
  
Qed.
    
Theorem permuteAndDouble_grouped_equiv : forall perm ws d ls,
  permuteAndDouble_grouped ws d perm = Some ls ->
  permuteAndDouble ws d (flatten perm) (endIndices perm) = Some (flatten ls).

  induction perm; intros; simpl in *.
  inversion H; clear H; subst.
  reflexivity.
  apply permuteAndDouble_grouped_cons in H.
  destruct H.
  destruct H.
  destruct H.
  intuition idtac; subst.
  apply IHperm in H0.
  simpl.
  erewrite permuteAndDouble_flatten_app_cons_if.
  replace ((x0 ++ wm_Double d :: nil) ++ flatten x1) with (x0 ++ wm_Double d :: (flatten x1)).
  reflexivity.
  rewrite <- app_assoc.
  simpl.
  reflexivity.
  trivial.
  eauto.
  eapply combineOpt_map_flatten in H1.
  trivial.
  reflexivity.
  intros.
  eapply decrExpLs_app; eauto.

Qed.

Theorem decrExpLs_flatten : forall d x2 x1,
  decrExpLs d (flatten x2) = Some x1 ->
  flatten (map (fun x => stripOptLs (decrExpLs d x)) x2) = x1.

  induction x2; intros; simpl in *.
  inversion H; clear H; subst.
  reflexivity.
  apply decrExpLs_app_if in H.
  destruct H.
  destruct H.
  intuition idtac; subst.
  apply IHx2 in H.
  subst.
  f_equal.
  rewrite H0.
  reflexivity.

Qed.

Theorem decrExpLs_combineOpt : forall d x2 x1,
  decrExpLs d (flatten x2) = Some x1 ->
  combineOpt (map (decrExpLs d) x2) =
  Some (map (fun x0 : list WindowedMultOp => stripOptLs (decrExpLs d x0)) x2).

  induction x2; intros; simpl in *.
  reflexivity.
  apply decrExpLs_app_if in H.
  destruct H.
  destruct H.
  intuition idtac; subst.
  rewrite H0.
  erewrite IHx2; eauto.
  
Qed.

Theorem permuteAndDouble_grouped_equiv_if : forall perm ws d ls,
  permuteAndDouble ws d (flatten perm) (endIndices perm) = Some ls -> 
  exists ls', permuteAndDouble_grouped ws d perm = Some ls' /\ flatten ls' = ls.

  induction perm; intros; simpl in *.
  unfold permuteAndDouble in *.
  simpl in *.
  inversion H; clear H; subst.
  exists nil.
  intuition idtac.
  apply permuteAndDouble_flatten_app_cons in H.
  destruct H.
  destruct H.
  destruct H.
  intuition idtac.
  subst.
  apply IHperm in H.
  destruct H.
  intuition idtac; subst.
  erewrite (@permuteAndDouble_grouped_cons_if _ _ _ _ _ x (map (fun x => stripOptLs (decrExpLs d x)) x2)); eauto.
  econstructor.
  intuition idtac; eauto.
  simpl.
  rewrite <- app_assoc.
  f_equal.
  simpl.
  f_equal.
  eapply decrExpLs_flatten; eauto.
  eapply decrExpLs_combineOpt; eauto.
  
Qed.


(* Machine semantics requires a group. The following section assumes an arbitrary group, and the semantics is defined
in terms of this group. The section also fixes a group element (usually the generator of some interesting group), and multiples
of this group element are added by the wm_Add operation. *)
Section MachineEval.

  Context `{grp : CommutativeGroupWithDouble}.

  Variable p : GroupElem.
  Variable RegularWindow : SignedWindow -> Prop.

  Variable wsize : nat.
  Hypothesis wsize_nz : wsize <> 0%nat.

  Variable bMultiple : SignedWindow -> GroupElem.
  Hypothesis bMultiple_correct : forall w, 
    RegularWindow w ->
    bMultiple w == groupMul_doubleAdd_signed w p.

  (* Semantics of a single double or add operation *)
  Definition evalWindowMult (m : WindowedMultOp)(e : GroupElem) :=
    match m with
    | wm_Add n w => (groupAdd (groupMul_doubleAdd_signed (zDouble_n (n * wsize) w) p) e)
    | wm_Double n => (groupDouble_n (n * wsize) e)
    end.

  Theorem evalWindowMult_compat : forall m e1 e2,
    e1 == e2 ->
    evalWindowMult m e1 == evalWindowMult m e2.

    intros.
    unfold evalWindowMult.
    destruct m.
    apply groupAdd_proper.
    reflexivity.
    trivial.
    apply groupDouble_n_equiv_compat;
    trivial.

  Qed.

  (* Semantics of a program comprising a list of operations that are executed in order *)
  Fixpoint groupMul_signedWindows_prog (ws : list WindowedMultOp) : GroupElem :=
    match ws with
    | nil => idElem
    | w :: ws' => evalWindowMult w (groupMul_signedWindows_prog ws')
    end.

  (* groupMul_signedWindows_exp takes a number n and a list of windows, and effectively
  multiplies each window by 2^(n + wsize) before performing the usual signed window multiplication operation. 
  This is an intermediate definition that simplifies an equivalence proof. *)
  Fixpoint groupMul_signedWindows_exp (ws : list SignedWindow) n : GroupElem :=
    match ws with
    | nil => idElem
    | w :: ws' => groupAdd (groupMul_doubleAdd_signed (zDouble_n (n * wsize) w) p) (groupMul_signedWindows_exp ws' (S n))
    end.

  Definition groupMul_signedWindows := groupMul_signedWindows wsize bMultiple.

  Theorem groupMul_signedWindows_exp_equiv : forall ws n,
    Forall RegularWindow ws ->
    groupDouble_n (wsize * n) (groupMul_signedWindows ws) == groupMul_signedWindows_exp ws n.

    induction ws; intros; simpl in *.
    apply groupDouble_n_id.

    unfold groupAdd_signedWindow.
    rewrite <- IHws.
    rewrite zDouble_n_mul; eauto.
    replace (wsize * S n)%nat with (n * wsize + wsize)%nat; try lia.
    rewrite groupDouble_n_add.
    rewrite groupAdd_groupDouble_n_distr.
    replace (wsize * n)%nat with (n * wsize)%nat; try lia.
    apply groupDouble_n_equiv_compat; eauto.
    apply groupAdd_proper.
    apply bMultiple_correct.
    inversion H; clear H; subst.
    trivial.
    reflexivity.
    inversion H; trivial.
  Qed.

  Theorem groupMul_signedWindows_prog_equiv : forall ws n,
    groupMul_signedWindows_prog (signedWindowsToProg ws n) == groupMul_signedWindows_exp ws n.

    induction ws; intros; simpl in *.
    reflexivity.
    rewrite IHws.
    reflexivity.

  Qed.

  Theorem evalWindowMult_double_equiv : forall n a w e,
    (decrExp n a) = Some w ->
    evalWindowMult a (groupDouble_n (n * wsize) e) == groupDouble_n (n * wsize) (evalWindowMult w e).

    intros.
    unfold decrExp, evalWindowMult in *.
    destruct a.
    destruct (le_dec n n0).
    inversion H; clear H; subst.
    rewrite zDouble_n_mul; eauto.
    assert (exists m, n + m = n0)%nat.
    exists (n0 - n)%nat.
    lia.
    destruct H. subst.
    rewrite Nat.mul_add_distr_r.
    rewrite groupDouble_n_add.
    rewrite groupAdd_groupDouble_n_distr; eauto.
    apply groupDouble_n_equiv_compat; eauto.
    apply groupAdd_proper.
    rewrite zDouble_n_mul; eauto.
    replace (n + x - n)%nat with x.
    reflexivity.
    lia.
    reflexivity.
    discriminate.

    inversion H; clear H; subst.  
    rewrite <- groupDouble_n_add.
    rewrite plus_comm.
    rewrite groupDouble_n_add.
    reflexivity.

  Qed.

  Theorem insertDouble_equiv_h : forall n ps ps',
    Some ps' = decrExpLs n ps ->
    groupMul_signedWindows_prog ps == groupDouble_n (n * wsize) (groupMul_signedWindows_prog ps').

    induction ps; intros; simpl in *.
    inversion H; clear H; subst.
    simpl.
    rewrite groupDouble_n_id; eauto.
    reflexivity.
    remember (decrExp n a) as z1. destruct z1.
    remember (decrExpLs n ps) as z2. destruct z2.
    inversion H; clear H; subst.
    simpl.
    transitivity (evalWindowMult a (groupDouble_n (n * wsize) (groupMul_signedWindows_prog l))).
    eapply evalWindowMult_compat; eauto.
    eapply evalWindowMult_double_equiv.
    symmetry.
    trivial.
    discriminate.
    discriminate.
  Qed.

  Theorem insertDouble_equiv : forall n ps ps',
    (insertDouble n ps) = Some ps' -> 
    groupMul_signedWindows_prog ps == groupMul_signedWindows_prog ps'.

    intros.
    unfold insertDouble in *.
    remember (decrExpLs n ps) as z.
    destruct z.
    inversion H; clear H; subst.
    simpl.
    eapply insertDouble_equiv_h; eauto.
    discriminate.
  Qed.

  Theorem swapFront_equiv_h : forall w w0 w1 w2 ps,
    Some (w1, w2) = swapPair w w0 ->
    groupMul_signedWindows_prog (w :: w0 :: ps) == groupMul_signedWindows_prog (w1 :: w2 :: ps).

    intros.
    simpl.
    unfold swapPair in *.
    destruct w.
    destruct w0.
    inversion H; clear H; subst.  
    unfold evalWindowMult. 
    repeat rewrite <- groupAdd_assoc.
    apply groupAdd_proper.
    apply groupAdd_comm.
    reflexivity.

    destruct (le_dec n0 n).
    inversion H; clear H; subst.
    assert (exists n1, n1 + n0 = n)%nat.
    exists (n - n0)%nat.
    lia.
    destruct H.
    subst.
    replace (x + n0 - n0)%nat with x.
    unfold evalWindowMult.
    rewrite zDouble_n_mul; eauto.
    rewrite Nat.mul_add_distr_r.
    rewrite plus_comm.
    rewrite groupDouble_n_add.
    rewrite groupAdd_groupDouble_n_distr; eauto.
    apply groupDouble_n_equiv_compat; eauto.
    apply groupAdd_proper.
    rewrite zDouble_n_mul; eauto.
    reflexivity.
    reflexivity.
    lia.
    discriminate.

    destruct w0.
    inversion H; clear H; subst.
    unfold evalWindowMult.
    symmetry.
    rewrite zDouble_n_mul; eauto.
    rewrite Nat.mul_add_distr_r.
    rewrite groupDouble_n_add.
    rewrite groupAdd_groupDouble_n_distr; eauto.
    apply groupDouble_n_equiv_compat; eauto.
    apply groupAdd_proper.
    rewrite zDouble_n_mul; eauto.
    reflexivity.
    reflexivity.

    inversion H; clear H; subst.
    unfold evalWindowMult.
    rewrite <- groupDouble_n_add; eauto.
    rewrite plus_comm.
    rewrite groupDouble_n_add.
    reflexivity.

  Qed.

  Theorem swapFront_equiv : forall ps ps',
    (swapFront ps) = Some ps' -> 
    groupMul_signedWindows_prog ps == groupMul_signedWindows_prog ps'.

    intros.
    unfold swapFront in *.
    destruct ps.
    discriminate.
    destruct ps.
    discriminate.
    remember (swapPair w w0) as z.
    destruct z.
    destruct p0.
    inversion H; clear H; subst.
    simpl.
    apply swapFront_equiv_h.
    trivial.
    discriminate.

  Qed.

  Theorem addProgPermEq : forall (ps1 ps2 : list WindowedMultOp),
    Permutation ps1 ps2 ->
    AddProg ps1 ->
    groupMul_signedWindows_prog ps1 == groupMul_signedWindows_prog ps2.

    induction 1; intros; simpl in *.
    reflexivity.

    apply evalWindowMult_compat.
    eapply IHPermutation.
    inversion H0; eauto.
    inversion H; clear H; subst.
    inversion H3; clear H3; subst.
    
    unfold evalWindowMult.
    destruct y.
    destruct x.
    repeat rewrite <- groupAdd_assoc.
    apply groupAdd_proper.
    rewrite groupAdd_comm.
    reflexivity.
    reflexivity.
    intuition idtac.
    intuition idtac.

    rewrite IHPermutation1.
    apply IHPermutation2.
    eauto.
    eapply Permutation_Forall.
    eauto.
    eauto.
    eauto.

  Qed.

  Theorem insertDoubleAt_equiv : forall n d ls ls',
    insertDoubleAt d ls n = Some ls' ->
    groupMul_signedWindows_prog ls == groupMul_signedWindows_prog ls'.

    induction n; intros; simpl in *.
    replace (insertDoubleAt d ls 0) with (insertDouble d ls) in H.
    eapply insertDouble_equiv.
    eauto.
    destruct ls; simpl in *.
    reflexivity.
    reflexivity.
    
    destruct ls; simpl in *.
    discriminate.
    case_eq (insertDoubleAt d ls n); intros;
    rewrite H0 in H.
    inversion H; clear H; subst.
    simpl.
    apply evalWindowMult_compat.
    eapply IHn.
    eauto.
    discriminate.

  Qed.

  Theorem insertDoublesAt_equiv : forall lsn d ls ls',
    insertDoublesAt d ls lsn = Some ls' ->
    groupMul_signedWindows_prog ls == groupMul_signedWindows_prog ls'.

    induction lsn; intros; simpl in *.
    inversion H; clear H; subst.
    reflexivity.
    
    case_eq (insertDoubleAt d ls a); intros;
    rewrite H0 in H.
    transitivity (groupMul_signedWindows_prog l).
    eapply insertDoubleAt_equiv; eauto.
    eauto.
    discriminate.
  Qed.

  (* Prove that programs produced by the permuteAndDouble function produce the same result
  as the function that performed group multiplication using signed windows defined in GroupMulWNAF.
  This existing function is already proved to be correct in GroupMulWNAF. Also, permuteAndDouble may fail,
  and this equivalence holds any time this function succeeds. *)
  Theorem permuteAndDouble_equiv : forall ws d perm doubles ps,
    Forall RegularWindow ws -> 
    Permutation perm (seq 0 (length ws)) ->
    permuteAndDouble ws d perm doubles = Some ps -> 
    groupMul_signedWindows_prog ps == groupMul_signedWindows ws.

    intros.
    unfold permuteAndDouble in *.
    case_eq (multiSelect (signedWindowsToProg ws 0) perm); intros;
    rewrite H2 in H1.
    transitivity (groupMul_signedWindows_prog l).
    symmetry.
    eapply insertDoublesAt_equiv; eauto.
    transitivity (groupMul_signedWindows_prog (signedWindowsToProg ws 0) ).
    symmetry.
    apply addProgPermEq.
    eapply multiSelect_perm; [idtac | eauto].
    rewrite signedWindowsToProg_length.
    trivial.
    apply signedWindowsToProg_AddProg.
    rewrite groupMul_signedWindows_prog_equiv.
    unfold groupMul_signedWindows_exp.
    rewrite <- groupMul_signedWindows_exp_equiv; eauto.
    rewrite Nat.mul_0_r.
    simpl.
    reflexivity.
    trivial.
    
    discriminate.

  Qed.

  Theorem permuteAndDouble_grouped_app: forall d a b ws ls,
    permuteAndDouble_grouped ws d (a ++ b) = Some ls ->
    exists ls1 ls2 ls3,
    permuteAndDouble_grouped ws d a = Some ls1 /\
    permuteAndDouble_grouped ws d b = Some ls2 /\ 
    combineOpt (List.map (decrExpLs ((List.length ls1) * d)) ls2) = Some ls3 /\
    ls = ls1 ++ ls3.

    intros.
    unfold permuteAndDouble_grouped in *.
    rewrite map_app in *.
    rewrite combineOpt_app in *.
    optSomeInv.
    apply decrExpsLs_app in H3.
    destruct H3.
    destruct H.
    destruct H.
    intuition idtac; subst.
    rewrite H0.
    rewrite H.
    econstructor.
    econstructor.
    exists (List.map (fun x => x ++ (List.cons (wm_Double d) List.nil)) x1).
    intuition idtac.
    rewrite map_length.
    rewrite List.map_map.
    erewrite (combineOpt_map_map _ (fun x => Some (x ++ (List.cons (wm_Double d) List.nil))) );[
    reflexivity | idtac | eauto | idtac].
    intros.
    eapply decrExpLs_app.
    replace (Datatypes.length x) with (Datatypes.length l0).
    eauto.
    eapply decrExpsLs_length; eauto.
    reflexivity.
    eapply combineOpt_f.
    eapply List.map_app.
  Qed.

End MachineEval.

(* Some alternative definitions and facts that are useful in proving that the "permute and double" operation succeeds *)
Definition decrExp'(n : nat) (n' : nat) :=  if Compare_dec.le_dec n n' then Some (n' - n)%nat else None.

Fixpoint decrExpLs' (n : nat) (ps : list nat)  :=
  match ps with
  | nil => Some nil
  | p :: ps' =>
      match decrExp' n p with
      | Some p' => match decrExpLs' n ps' with
                   | Some ps'' => Some (p' :: ps'')
                   | None => None
                   end
      | None => None
      end
  end.

Fixpoint decrExpsLs' (n : nat) (ps : list (list nat)) : option (list (list nat)) :=
match ps with
| nil => Some nil
| p :: ps' =>
    match decrExpsLs' n ps' with
    | Some x => match combineOpt (List.map (decrExpLs' n) x) with
                | Some x' => Some (p :: x')
                | None => None
                end
    | None => None
    end
end.

Definition wmIsMultiple (y : nat)(x : WindowedMultOp) :=
  match x with
  | wm_Add n w => Nat.gcd n y = y
  | wm_Double  n => True
  end.

Theorem multiSelect_signedWindowsToProg_Some :  forall a0 ws,
  List.Forall (fun x => x < List.length ws) a0 -> 
  exists b0 : list WindowedMultOp,
  multiSelect (signedWindowsToProg ws 0) a0 = Some b0 /\
  List.Forall2 (fun (x : nat) (y : WindowedMultOp) => exists w : Z, y = wm_Add x w) a0 b0.

  induction a0; intros; simpl in *.
  inversion H; clear H; subst.
  exists List.nil.
  intuition idtac.
  econstructor.

  inversion H; clear H; subst.
  eapply IHa0 in H3.
  destruct H3.
  destruct H.
  unfold multiSelect in *.
  simpl.
  edestruct (@nth_error_Some_ex  _ a (signedWindowsToProg ws 0)).
  rewrite signedWindowsToProg_length.
  lia.    
  pose proof H1.
  eapply nth_error_signedWindowsToProg_Some_add in H1.
  destruct H1.
  intuition idtac; subst; simpl in *.
  rewrite H3.
  rewrite H.
  econstructor; intuition idtac.
  econstructor.
  econstructor.
  reflexivity.
  apply H0.
Qed.

Theorem decrExpLs'_Some_eq : forall perm perm' x,
  decrExpLs' 1 perm = Some perm' ->  
  List.Forall2 (fun (x : nat) (y : WindowedMultOp) => exists w : Z, y = wm_Add x w) perm x -> 
  exists y, decrExpLs 1 x = Some y /\  List.Forall2 (fun (x : nat) (y : WindowedMultOp) => exists w : Z, y = wm_Add x w) perm' y.

  induction perm; intros; simpl in *.
  optSomeInv.
  inversion H0; clear H0; subst.
  simpl.
  econstructor.
  split.
  reflexivity.
  econstructor.
  
  optSomeInv.
  inversion H0; clear H0; subst.
  edestruct IHperm; eauto.
  destruct H.
  simpl.
  rewrite H.
  destruct H4. subst.
  
  unfold decrExp' in *.
  destruct (Compare_dec.le_dec 1 a).
  optSomeInv.   
  unfold decrExp.
  destruct (Compare_dec.le_dec 1 a).
  econstructor.
  split.
  reflexivity.
  econstructor; trivial.
  econstructor.
  reflexivity.
  lia.
  discriminate.

Qed.


Theorem map_decrExpLs'_Some_eq : forall perm perm' x,
  combineOpt (List.map (decrExpLs' 1) perm) = Some perm' ->  
  List.Forall2 (List.Forall2 (fun (x : nat) (y : WindowedMultOp) => exists w : Z, y = wm_Add x w)) perm x -> 
  exists y, combineOpt (List.map (decrExpLs 1) x) = Some y /\  List.Forall2 (List.Forall2 (fun (x : nat) (y : WindowedMultOp) => exists w : Z, y = wm_Add x w)) perm' y.

  induction perm; intros; simpl in *.
  optSomeInv.
  inversion H0; clear H0; subst.
  simpl.
  econstructor.
  split.
  reflexivity.
  econstructor.

  optSomeInv.
  inversion H0; clear H0; subst.
  edestruct IHperm; eauto.
  destruct H.
  simpl.
  rewrite H.
  edestruct decrExpLs'_Some_eq; eauto.
  destruct H3.
  rewrite H3.
  econstructor.
  split.
  reflexivity.
  econstructor; trivial.    

Qed. 

Theorem decrExpsLs'_Some_eq : forall perm perm' x,
  decrExpsLs' 1 perm = Some perm' ->
  List.Forall2 (List.Forall2 (fun (x : nat) (y : WindowedMultOp) => exists w : Z, y = wm_Add x w)) perm x -> 
  exists y, decrExpsLs 1 x = Some y /\  List.Forall2 (List.Forall2 (fun (x : nat) (y : WindowedMultOp) => exists w : Z, y = wm_Add x w)) perm' y. 

  induction perm; intros; simpl in *.
  optSomeInv.
  inversion H0; clear H0; subst.
  simpl.
  econstructor.
  split.
  reflexivity.
  econstructor.

  optSomeInv.
  inversion H0; clear H0; subst.
  simpl.
  edestruct IHperm; eauto.
  destruct H.
  rewrite H.
  edestruct map_decrExpLs'_Some_eq; eauto.
  destruct H3.
  rewrite H3.
  econstructor.
  split.
  reflexivity.
  econstructor; trivial.

 Qed.

Theorem permuteAndDouble_grouped_Some : forall d ws perm perm',
  List.Forall (List.Forall (fun x : nat => x < Datatypes.length ws)) perm -> 
  d = List.length perm -> 
  decrExpsLs' 1 perm = Some perm' ->
  List.Forall (List.Forall (fun y => Nat.gcd y d= d)) perm' -> 
  exists x, permuteAndDouble_grouped ws 1 perm = Some x /\ 
  List.Forall (List.Forall (wmIsMultiple d)) x.

  intros.
  unfold permuteAndDouble_grouped.
  subst.
  edestruct (@combineOpt_map_Some _ _  (multiSelect (signedWindowsToProg ws 0)) perm (List.Forall (fun x => x < List.length ws))  (List.Forall2 (fun x y => exists w, y = wm_Add x w))).
  trivial.
  intros.
  eapply multiSelect_signedWindowsToProg_Some.
  trivial.
  destruct H0.
  rewrite H0.
  edestruct (@decrExpsLs'_Some_eq perm perm' x); eauto.
  destruct H4.
  rewrite H4.
  econstructor.
  econstructor.
  reflexivity.

  eapply Forall_map.
  apply (@Forall_Forall2_impl _ _ _ x0) in H2.
  eapply (@Forall2_Forall_impl _ _ _ perm').
  eapply forall2_symm.
  eapply Forall2_impl_2.
  eapply H2.
  eapply H5.
  intros.
  simpl in *.
  destruct H6.
  eapply Forall_app.
  split.
  apply (@Forall_Forall2_impl _ _ _ a) in H6.
  eapply (@Forall2_Forall_impl _ _ _ b).
  eapply forall2_symm.
  eapply Forall2_impl_2.
  eapply H6.
  eapply H7.
  intros.
  simpl in *.
  destruct H8.
  destruct H9.
  subst.
  unfold wmIsMultiple.
  trivial.
  symmetry.
  eapply Forall2_length; eauto.
  econstructor.
  unfold wmIsMultiple.
  trivial.
  econstructor.
  symmetry.
  eapply Forall2_length; eauto.

Qed.

Theorem lsMultiples_all_lt : forall z x y,
  List.Forall (fun x0 : nat => x0 < z) (lsMultiples z x y).

  induction z; intros; simpl in *.
  econstructor.

  eapply Forall_app.
  split.
  eapply List.Forall_impl; eauto.
  intros; simpl in *.
  lia.

  destruct (isMultiple z x y); econstructor.
  lia.
  econstructor.

Qed.

Theorem groupIndices_h_all_lt : forall  y z x,
  List.Forall (List.Forall (fun x : nat => x < z)) (groupIndices_h z x y).

  induction y; intros; simpl in *.
  econstructor.

  eapply Forall_app.
  split; eauto.
  econstructor.
  eapply lsMultiples_all_lt.
  econstructor.
 

Qed.

Theorem groupIndices_all_lt : forall nw x,
  List.Forall (List.Forall (fun x : nat => x < nw)) (groupIndices nw x).

  intros.
  apply groupIndices_h_all_lt.

Qed.
