(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0 *)

(* Some general purpose definitions and theory. *)

Set Implicit Arguments.

Require Import BinNat.
Require Import BinPos.
Require Import Pnat.
Require Import Nat.
Require Import List.
Require Import Arith.
Require Import Arith.Peano_dec.
Require Import Arith.Compare_dec.
Require Import Bool.
Require Import micromega.Lia.
Require Import ZArith.BinInt.
Require Import ZArith.
Require Import Permutation.

Local Open Scope Z_scope.

Theorem Z_odd_lor_1 : forall z,
  Z.odd z = true ->
  Z.lor z 1 = z.

  intros.
  eapply Z.bits_inj_iff'; intros.
  replace 1 with (2^0).
  rewrite <- Z.setbit_spec'.
  rewrite Z.setbit_eqb; try lia.
  case_eq (Z.eqb 0 n); intros; simpl; trivial.
  rewrite Z.eqb_eq in H1; subst.
  rewrite Z.bit0_odd. congruence.
  trivial.

Qed.

Theorem even_prod_2 : forall x,
  Z.even x = true ->
  exists y, x = 2 * y.

  intros.
  apply Z.even_spec in H.
  apply H.

Qed.

Theorem Z_even_lor_1 : forall z,
  Z.even z = true ->
  Z.lor z 1 = Z.succ z.

  intros.
  replace 1 with (2^0).
  rewrite <- Z.setbit_spec'.
  eapply Z.bits_inj_iff'; intros.
  rewrite Z.setbit_eqb; try lia.
  case_eq (Z.eqb 0 n); intros; simpl; trivial.
  rewrite Z.eqb_eq in H1; subst.
  rewrite Z.bit0_odd. 
  rewrite Z.odd_succ.
  congruence.
  destruct (even_prod_2 z); trivial; subst.

  rewrite Z.eqb_neq in H1.
  replace n with (Z.succ (Z.pred n)); try lia.
  rewrite Z.testbit_even_succ; trivial.
  rewrite <- Z.add_1_r.
  rewrite Z.testbit_odd_succ.
  reflexivity.
  lia.
  lia.
  trivial.

Qed.

Theorem Z_even_lt : forall z1 z2,
  Z.even z1 = true ->
  Z.even z2 = true ->
  z1 < z2 ->
  (Z.succ z1) < z2.

  intros.
  assert (Z.succ z1 <> z2).
  rewrite <- Z_even_lor_1; trivial.
  intuition.
  rewrite <- Z.bits_inj_iff' in H2.
  specialize (H2 0); intuition.
  assert (0 <= 0) by lia; intuition.
  replace 1 with (Z.pow 2 0) in H4; trivial.
  rewrite <- Z.setbit_spec' in H4.
  rewrite Z.setbit_eq in H4; try lia.
  rewrite Z.bit0_odd in H4.
  rewrite <- Z.negb_even in H4.
  rewrite H0 in H4.
  simpl in *.
  discriminate.

  lia.

Qed.

Theorem nat_shiftl_nz : forall n b,
  (0 < b)%nat ->
  (0 < shiftl b n)%nat.

  induction n; intros; simpl in *.
  lia.
  unfold double.
  specialize (IHn b).
  lia.
  
Qed.

Theorem Z_shiftl_1 : forall z,
  Z.shiftl z 1 = Z.double z.

  intuition.

Qed.

Theorem shiftl_to_nat_eq : forall n2 n1,
  (shiftl n1 n2) = Z.to_nat (Z.shiftl (Z.of_nat n1) (Z.of_nat n2)).

  induction n2; intros.
  simpl. lia.
  rewrite Znat.Nat2Z.inj_succ.
  simpl.
  rewrite IHn2.
  rewrite <- Z.add_1_r.
  rewrite <- Z.shiftl_shiftl.
  rewrite Z_shiftl_1.
  rewrite Z.double_spec.
  rewrite Znat.Z2Nat.inj_mul.
  unfold double.
  simpl.
  lia.
  lia.
  apply Z.shiftl_nonneg.
  lia.
  lia.
  
Qed.

Theorem Z_of_nat_0_if : forall n,
  Z.of_nat n = 0 ->
  n = 0%nat.

  intuition idtac.
  destruct n; simpl in *; trivial.
  discriminate.

Qed.

Definition zDouble_n (times : nat) n : Z :=
  Z.shiftl n (Z.of_nat times).

Theorem zDouble_n_S : forall n z,
  zDouble_n (S n) z = Z.double (zDouble_n n z).
  
  unfold zDouble_n in *; intuition.
  rewrite Znat.Nat2Z.inj_succ.
  rewrite <- Z.add_1_l.
  rewrite <- Z.shiftl_shiftl.
  rewrite <- Z_shiftl_1.
  repeat rewrite Z.shiftl_shiftl.
  rewrite Z.add_comm.
  reflexivity.
  apply Znat.Nat2Z.is_nonneg.
  lia.
  lia.

Qed.

Theorem zDouble_n_0 : forall z,
  zDouble_n 0 z = z.
  
  unfold zDouble_n in *; intuition.

Qed.

Theorem Z_double_sum : forall z,
  Z.double z = z + z.

  intuition idtac.
  rewrite Z.double_spec.
  rewrite <- Z.add_diag.
  reflexivity.

Qed.

Theorem zDouble_n_0_r : forall n,
  zDouble_n n 0 = 0.

  unfold zDouble_n in *; intros.
  repeat rewrite Z.shiftl_mul_pow2.
  apply Z.mul_0_l.
  lia.
Qed.

Theorem zDouble_n_sum : forall n1 n2 z,
  zDouble_n (n1 + n2) z = zDouble_n n1 (zDouble_n n2 z).

  intros.
  unfold zDouble_n in *.
  rewrite Z.shiftl_shiftl.
  f_equal.
  lia.
  lia.

Qed.

Theorem zDouble_add_distr : forall n z1 z2,
  zDouble_n n (z1 + z2) = (zDouble_n n z1) + (zDouble_n n z2).

  unfold zDouble_n in *; intros.
  repeat rewrite Z.shiftl_mul_pow2.
  rewrite Z.mul_add_distr_r.
  reflexivity.
  lia.
  lia.
  lia.
Qed.

Theorem zDouble_n_opp : forall n z,
  - (zDouble_n n z) = zDouble_n n (-z).

  intros.    
  unfold zDouble_n in *.
  repeat rewrite Z.shiftl_mul_pow2.
  rewrite Z.mul_opp_l.
  reflexivity.
  lia.
  lia.

Qed.

Theorem zDouble_n_le_mono_r : forall n x1 x2,
  (0 <= n)%nat ->
  x1 <= x2 ->
  zDouble_n n x1 <= zDouble_n n x2.

  intros. unfold zDouble_n.
  repeat rewrite Z.shiftl_mul_pow2.
  apply Z.mul_le_mono_nonneg_r.
  apply Z.pow_nonneg; lia.
  trivial.
  lia.
  lia.
Qed.

Theorem even_of_pos_equiv : forall x,
  even (Pos.to_nat x) = Z.even (Z.pos x).

  destruct x; intuition; simpl in *.
  rewrite Pmult_nat_mult in *.
  case_eq (Pos.to_nat x * 2)%nat; intros; trivial.
  rewrite <- PeanoNat.Nat.odd_succ.
  rewrite <- H.
  rewrite <- PeanoNat.Nat.negb_even.
  apply negb_false_iff.
  rewrite PeanoNat.Nat.even_mul.
  apply orb_true_iff.
  intuition.

  unfold Pos.to_nat. simpl.
  rewrite Pmult_nat_mult.
  rewrite PeanoNat.Nat.even_mul.
  apply orb_true_iff.
  intuition.

Qed.

Theorem even_of_nat_equiv : forall n,
  even n = Z.even (Z.of_nat n).

  intros.
  remember (Z.of_nat n) as z.
  destruct z.
  symmetry in Heqz.
  apply Z_of_nat_0_if in Heqz; subst; trivial.

  rewrite <- Znat.positive_nat_Z in Heqz.
  rewrite Znat.Nat2Z.inj_iff in Heqz.
  subst.
  apply even_of_pos_equiv.

  lia.

Qed.

Theorem mod_div_prod : forall a b c,
  0 < b ->
  c <> 0 ->
  (a / c) mod b = (a mod (b * c)) / c.

  intuition.
  rewrite Z.mul_comm.
  rewrite Z.rem_mul_r; intuition.
 
  rewrite Z.mul_comm.
  rewrite Z.div_add; intuition.
  rewrite Zdiv.Zmod_div.
  rewrite Z.add_0_l.
  reflexivity.

Qed.

Theorem shiftl_pos: forall a n : Z, 
  0 <= n ->
  a > 0 ->
  Z.shiftl a n > 0.

  intuition.
  rewrite Z.shiftl_mul_pow2.
  apply Z.lt_gt.
  apply Z.mul_pos_pos.
  lia.
  apply Z.pow_pos_nonneg.
  lia.
  trivial.
  trivial.

Qed.

Theorem pow_mod_0 : forall x y,
  0%nat <> y ->
  x ^ (Z.of_nat y) mod x = 0.

  destruct y; intuition.
  rewrite Znat.Nat2Z.inj_succ.
  rewrite Z.pow_succ_r.
  rewrite Z.mul_comm.
  apply Zdiv.Z_mod_mult.
  lia.

Qed.

Theorem Zmod_mod_gen : forall a b c,
  0 < b ->
  0 < c ->
  b mod c = 0 ->
  (a mod b) mod c = a mod c.

  intuition.
  
  rewrite (Zdiv.Zmod_eq _ b); trivial.
  rewrite <- Zdiv.Zminus_mod_idemp_r.
  rewrite <- Zdiv.Zmult_mod_idemp_r.
  rewrite H1.
  rewrite Z.mul_0_r.
  rewrite Z.mod_0_l.
  rewrite Z.sub_0_r.
  reflexivity.
  lia.
  lia.

Qed.


Theorem zDouble_n_id : forall n,
  zDouble_n n 0 = 0.

  intuition.
  apply Z.shiftl_0_l.
Qed.

Theorem Zdouble_shiftl : forall x y,
  0 <= y ->
  Z.double (Z.shiftl x y) = Z.shiftl x (y + 1).

  intros.
  rewrite <- Z_shiftl_1.
  rewrite Z.shiftl_shiftl.
  reflexivity.
  trivial.

Qed.

Theorem mul_add_mod_ne : forall x a1 a2 b1 b2,
  (b1 < x)%nat ->
  (b2 < b1)%nat -> 
  (a1 * x + b1)%nat = (a2 * x + b2)%nat ->
  False.

  intros.
  rewrite Nat.mul_comm in H1.
  rewrite (Nat.mul_comm a2) in H1.
  apply Nat.div_mod_unique in H1.
  intuition idtac.
  lia.
  lia.
  lia.

Qed.


Theorem mod_clear_lt : forall a b n,
  0 < b ->
  (b | n) ->
  a < n ->
  a - (a mod b) <= n - b.

  intros.
  rewrite Z.mod_eq.
  rewrite Z.sub_sub_distr.
  rewrite Z.sub_diag.
  rewrite Z.add_0_l.
  assert (a / b <= (n / b) - 1).
  assert (a / b < n / b).
  destruct H0; subst.
  rewrite Zdiv.Z_div_mult.
  apply Z.div_lt_upper_bound.
  trivial.
  rewrite Z.mul_comm.
  trivial.
  lia.

  lia.
  eapply Z.le_trans.
  apply Z.mul_le_mono_nonneg_l.
  lia.
  eauto.
  rewrite Z.mul_sub_distr_l.
  rewrite Z.mul_1_r.
  apply Z.sub_le_mono_r.
  apply Zdiv.Z_mult_div_ge.
  lia.
  lia.
  
Qed.

Theorem Zshiftl_divide : forall x1 x2 z,
  0 <= x1 ->
  0 <= x2 ->
  x1 <= x2 ->
  Z.divide (Z.shiftl z x1) (Z.shiftl z x2).

  intros.
  replace x2 with (x1 + (x2 - x1)).
  rewrite <- Z.shiftl_shiftl.
  rewrite (Z.shiftl_mul_pow2 _ (x2 - x1)); [idtac | lia].
  apply Z.divide_factor_l.
  trivial.
  lia.

Qed.

Theorem Zdiv_lt_compat : forall a b c,
  (c | b) ->
  0 < c ->
  a < b ->
  a / c < b / c.

  intros.
  destruct H. subst.
  rewrite Z.div_mul.
  apply Z.div_lt_upper_bound;
  trivial.
  rewrite Z.mul_comm.
  trivial.
  lia.

Qed.

Theorem Z_ldiff_1_odd_sub : forall x,
  Z.odd (Z.pos x) = true -> 
  (Z.ldiff (Z.pos x) 1) = (Z.pos x)-1.

  intros.
  replace 1 with (2^0).
  rewrite <- Z.clearbit_spec'.
  destruct x; simpl in *. reflexivity.
  discriminate.
  trivial.
  trivial.

Qed.


Theorem lt_id_double_lt : forall n1 n2,
  (double n1 < double n2)%nat ->
  (n1 < n2)%nat.

  induction n1; intros; unfold double in *; simpl in *.
  destruct n2; simpl in *; intuition eauto.
  lia.
  destruct n2; simpl in *.
  lia.
  apply lt_n_S.
  eapply IHn1.
  lia.

Qed.

Theorem lt_if_shiftl_lt : forall n3 n1 n2,
  (shiftl n1 n3 < shiftl n2 n3)%nat ->
  (n1 < n2)%nat.

  induction n3; intuition; simpl in *.
  eapply IHn3.
  eapply lt_id_double_lt.
  trivial.

Qed.


Theorem double_div2_le : forall n,
  (double (div2 n) <= n)%nat.

  intros.
  rewrite (@Nat.div2_odd n) at 2.
  rewrite <- plus_0_r at 1.
  apply plus_le_compat.
  unfold double. simpl.
  rewrite Nat.add_0_r.
  reflexivity.
  lia.

Qed.

Theorem div2_shiftr_swap : forall n2 n1,
  div2 (shiftr n1 n2) = shiftr (div2 n1) n2.

  induction n2; intuition; simpl in *.
  rewrite IHn2.
  reflexivity.
Qed.


Theorem double_le_compat : forall a b,
  (a <= b)%nat ->
  (double a <= double b)%nat.

  unfold double. intros. simpl.
  eapply plus_le_compat; trivial.

Qed.

Theorem shiftl_shiftr_le : forall n1 n2,
  (shiftl (shiftr n2 n1) n1 <= n2)%nat.

  induction n1; intros; simpl in *.
  reflexivity.
  rewrite div2_shiftr_swap.
  specialize (IHn1 (div2 n2)).
  eapply le_trans.
  eapply double_le_compat; eauto.
  apply double_div2_le.

Qed.

Theorem nat_ind_strong :
 forall P,
  (forall n, (forall m, m < n -> P m)%nat -> P n) ->
  forall n, P n.

  intros.
  assert (forall x, (x <= n)%nat -> P x).
  induction n; intros.
  eapply X.
  intros.
  lia.

  eapply X.
  intros.
  eapply IHn. 
  lia.

  eapply X0.
  trivial.

Qed.

Theorem div2_to_nat_eq : forall n,
  div2 n = Z.to_nat (Z.div2 (Z.of_nat n)).

  induction n using nat_ind_strong; intros.
  destruct n. simpl. reflexivity.
  destruct n. simpl. reflexivity.
  repeat rewrite Znat.Nat2Z.inj_succ.
  simpl.
  rewrite H.
  repeat rewrite Z.div2_div.
  replace (Z.succ (Z.succ (Z.of_nat n))) with (1*2 + (Z.of_nat n)).
  rewrite Zdiv.Z_div_plus_full_l.
  rewrite Znat.Z2Nat.inj_add.
  simpl.
  reflexivity.
  lia.
  apply Z.div_pos.
  lia.
  lia.
  lia.
  lia.
  lia.   

Qed.

Theorem shiftr_to_nat_eq : forall n2 n1,
  0 <= n1 ->
  (Z.to_nat (Z.shiftr n1 (Z.of_nat n2))) = shiftr (Z.to_nat n1) n2.

  induction n2; intros.
  simpl in *.
  rewrite Z.shiftr_0_r.
  reflexivity.
  
  rewrite Znat.Nat2Z.inj_succ.
  simpl.
  rewrite <- IHn2.
  rewrite <- Z.add_1_r.
  rewrite <- Z.shiftr_shiftr.
  rewrite <- Z.div2_spec.
  rewrite div2_to_nat_eq. 
  rewrite Znat.Z2Nat.id.
  reflexivity.
  apply Z.shiftr_nonneg.
  trivial.
  lia.
  trivial.

Qed.

Theorem Z_sub_range_le_lt_dbl_pos : forall x y,
  (0 <= x ->
  0 <= y < 2 * x ->
  -x <= y - x < x)%Z.

  intros.
  lia.

Qed.

Theorem bound_abstract : forall x1 x2 y1 y2 z,
  (x1 <= z < y1 ->
  x2 <= x1 ->
  y1 <= y2 ->
  x2 <= z < y2)%Z.

  intuition idtac.
  eapply Z.le_trans; eauto.
  eapply Z.lt_le_trans; eauto.

Qed.

Theorem nat_shiftl_gt_base : forall n2 n1,
  (0 < n2 ->
  0 < n1 ->
  n1 < Nat.shiftl n1 n2)%nat.

  induction n2; intros; simpl in *.
  lia.
  destruct n2.
  simpl.
  unfold Nat.double.
  lia.
  assert (n1 < Nat.shiftl n1 (S n2))%nat.
  eapply IHn2; lia.
  unfold Nat.double.
  lia.
  
Qed.

Theorem div2_lt : forall x y ,
  (x < 2*y ->
  Z.div2 x < y)%Z.

  intros.
  rewrite Z.div2_div.
  apply Z.div_lt_upper_bound; lia.

Qed.



Fixpoint flatten (A : Type)(ls : list (list A)) : list A :=
  match ls with
  | nil => nil
  | x :: ls' => x ++ (flatten ls')
  end.

Theorem flatten_app : forall (A : Type)(ls1 ls2 : list (list A)),
  flatten (ls1 ++ ls2) = (flatten ls1 ++ flatten ls2).

  induction ls1; intros; simpl in *.
  reflexivity.
  rewrite <- app_assoc.
  f_equal.
  eauto.

Qed.

Fixpoint natToBits numBits (n : nat) : list bool :=
  match numBits with
  | 0%nat => nil
  | S numBits' => (if (eq_nat_dec (n mod 2) 1) then true else false) :: (natToBits numBits' (n/2))
  end.

Fixpoint natFromBits (bs : list bool) : nat :=
  match bs with
  | nil => 0
  | b :: bs' => (if b then 1 else 0) + (2 * (natFromBits bs'))
end.

Fixpoint forNats n :=
  match n with
    | O => nil
    | S n' => n' :: (forNats n')
  end.

Theorem forNats_length : forall n,
  List.length (forNats n) = n.

  induction n; intros; simpl in *; trivial.
  congruence.

Qed.

Theorem fold_app_length : forall (A B : Type) f (ls : list B) (acc : list A),
  length (fold_left (fun x y => x ++ ((f x y)::nil)) ls acc) = (List.length ls + List.length acc)%nat.

  induction ls; intros; simpl in *.
  trivial.
  rewrite IHls.
  rewrite app_length.
  simpl.
  lia.
Qed.

Theorem last_nth_equiv : forall (A : Type)(def : A)(ls : list A),
  last ls def = nth (pred (length ls)) ls def.

  induction ls; intuition; simpl in *.
  rewrite IHls.
  destruct ls; simpl in *; trivial.

Qed.

Theorem last_nth_equiv_gen
 : forall (A : Type) (def : A) (ls : list A) n,
  n = (Nat.pred (Datatypes.length ls)) ->
   List.last ls def =
   List.nth n ls
     def.

  intros. 
  subst.
  apply last_nth_equiv.

Qed.


(* A tactic that simplifies hypothesis involving option values*)
Ltac optSomeInv_1 := 
  match goal with 
    | [H : match ?a with | Some _ => _ | None => _ end = Some _ |- _ ] =>
      case_eq a; [ intro | idtac]; (let v := fresh in intro v; rewrite v in H); [idtac | discriminate]
    | [H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
    end.

Ltac optSomeInv := repeat optSomeInv_1.

(* Combine a list of option into an option list *)
Fixpoint combineOpt(A: Type)(ls : list (option A)) :=
  match ls with
  | nil => Some nil
  | opta :: ls' => 
    match opta with
    | None => None
    | Some a =>
      match (combineOpt ls') with
      | None => None
      | Some ls'' => Some (a :: ls'')
      end
    end
  end.

Theorem combineOpt_perm_ex : forall (A : Type)(ls1 ls2 : list (option A)),
  Permutation ls1 ls2 ->
  forall ls1', 
  combineOpt ls1 = Some ls1' ->
  exists ls2', 
  combineOpt ls2 = Some ls2' /\
  Permutation ls1' ls2'.

  induction 1; intros; simpl in *.
  inversion H; clear H; subst.
  exists nil.
  intuition idtac.
  econstructor.

  destruct x; simpl in *.
  remember (combineOpt l) as z.
  destruct z.
  inversion H0; clear H0; subst.
  destruct (IHPermutation l0).
  reflexivity.
  intuition idtac.
  exists (a :: x).
  rewrite H1.
  intuition idtac.
  econstructor.
  trivial.
  discriminate.
  discriminate.

  destruct y; try discriminate.
  destruct x; try discriminate.
  remember (combineOpt l) as z1; destruct z1.
  inversion H; clear H; subst.
  exists (a0 :: a :: l0).
  intuition idtac.
  econstructor.
  discriminate.

  destruct (IHPermutation1 ls1').
  trivial.
  intuition idtac.
  destruct (IHPermutation2 x).
  trivial.
  intuition idtac.
  exists x0.
  intuition idtac.
  econstructor; eauto.

Qed.

Theorem NoDup_app : forall (A : Type)(ls1 ls2 : list A),
  NoDup ls1 -> 
  NoDup ls2 -> 
  (forall a, In a ls1 -> In a ls2 -> False) -> 
  NoDup (ls1 ++ ls2).

  induction ls1; intros; simpl in *.
  trivial.
  inversion H; clear H; subst.
  eapply (@Permutation_NoDup _ (ls1 ++ (a :: ls2))).
  eapply Permutation_sym.
  eapply Permutation_middle.
  eapply IHls1.
  trivial.
  econstructor.
  intuition idtac.
  eapply H1.
  left.
  reflexivity.
  trivial.
  trivial.
  intuition idtac.
  inversion H2; clear H2; subst.
  intuition idtac.
  eauto.

Qed.


Theorem nth_error_skipn_eq : forall n3 (A : Type)(ls : list A) n1,
  (n3 <= n1)%nat ->
  nth_error ls n1 = nth_error (skipn n3 ls) (n1 - n3).

  induction n3; intros; simpl in *.
  rewrite Nat.sub_0_r.
  reflexivity.

  destruct n1.
  lia.
  simpl.
  
  destruct ls.
  symmetry.
  apply nth_error_None.
  simpl.
  lia.
  eapply IHn3.
  lia.

Qed.

Theorem nth_error_seq_skipn_eq : forall n2 (A : Type)(ls : list A) n1 n3,
  (n3 <= n1)%nat ->
  map (nth_error ls) (seq n1 n2) = map (nth_error (skipn n3 ls)) (seq (n1 - n3) n2).

  induction n2; intros; simpl in *.
  trivial.
  f_equal.
  eapply nth_error_skipn_eq.
  lia.
  specialize (IHn2 _ ls (S n1) n3).
  rewrite IHn2.
  replace (S n1 - n3)%nat with (S (n1 - n3)).
  reflexivity.
  lia.
  lia.
Qed.

Theorem combineOpt_map_seq_eq : forall (A : Type)(ls : list A),
  combineOpt (map (nth_error ls) (seq 0 (length ls))) = Some ls.

  induction ls; intros; simpl in *.
  reflexivity.
  rewrite (@nth_error_seq_skipn_eq _ _ _ _ 1%nat).
  simpl.
  rewrite IHls.
  reflexivity.
  trivial.

Qed.

(* Select a number of items from a list based on index *)
Definition multiSelect(A : Type)(ls : list A)(lsn : list nat) : option (list A) :=
  combineOpt (map (nth_error ls) lsn).


Theorem multiSelect_perm : forall (A : Type)(ls ls' : list A)(lsn : list nat),
  Permutation lsn (seq O (length ls)) ->
  multiSelect ls lsn = Some ls' ->
  Permutation ls ls'.

  intros.
  unfold multiSelect in *.
  assert (combineOpt (map (nth_error ls) (seq 0 (length ls))) = Some ls).
  apply combineOpt_map_seq_eq.

  eapply combineOpt_perm_ex in H0.
  destruct H0.
  intuition idtac.
  rewrite H1 in H2.
  inversion H2; clear H2; subst.
  eapply Permutation_sym.
  trivial.
  apply Permutation_map.
  trivial.

Qed.

Theorem multiSelect_in_range_Some : forall (A : Type)(ls : list A)(lsn : list nat),
  (forall n, In n lsn -> n < length ls)%nat ->
  exists ls', multiSelect ls lsn = Some ls'.

  induction lsn; intros; simpl in *.
  exists nil.
  reflexivity.
  edestruct (IHlsn).
  intros.
  apply H.
  intuition idtac.
  unfold multiSelect in *.
  simpl.
  case_eq (nth_error ls a); intros.
  rewrite H0.
  econstructor; eauto.
  apply nth_error_None in H1.
  specialize (H a).
  intuition idtac.
  lia.

Qed.

Theorem multiSelect_perm_Some : forall (A : Type)(ls : list A)(lsn : list nat),
  Permutation lsn (seq O (length ls)) -> 
  exists ls', multiSelect ls lsn = Some ls'.

  intros.
  apply multiSelect_in_range_Some.
  intros.
  eapply Permutation_in in H0; eauto.
  apply in_seq in H0.
  lia.
  
Qed.


 Theorem combineOpt_app : forall ( A: Type)(ls1 ls2 : list (option A)),
  combineOpt (ls1 ++ ls2) = 
  match (combineOpt ls1) with
  | Some ls1' => 
    match (combineOpt ls2) with
    | Some ls2' => Some (ls1' ++ ls2')
    | None => None
    end
  | None => None
  end.

  induction ls1; intros; simpl in *.
  destruct (combineOpt ls2); reflexivity.
  destruct a.
  rewrite IHls1.
  destruct (combineOpt ls1).
  destruct (combineOpt ls2).
  simpl.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
Qed.

Theorem combineOpt_id : forall (A : Type)(ls : list A),
  combineOpt (List.map (fun x => Some x) ls) = Some ls.

  induction ls; intros; simpl in *.
  reflexivity.
  rewrite IHls.
  reflexivity.
  
Qed.

Theorem combineOpt_map_map : forall (A B C : Type) f1 f2 f3 (ls1 : list A) (ls2: list B) (ls3 : list C),
  (forall x y, f1 x = Some y -> f3 x = f2 y) ->
  combineOpt (List.map f1 ls1) = Some ls2 ->
  combineOpt (List.map f2 ls2) = Some ls3 -> 
  combineOpt (List.map f3 ls1) = Some ls3.

  induction ls1; intros; simpl in *.
  inversion H0; clear H0; subst.
  simpl in *.
  inversion H1; clear H1; subst.
  reflexivity.
  case_eq (f1 a); intros;
  rewrite H2 in H0.
  case_eq (combineOpt (List.map f1 ls1)); intros;
  rewrite H3 in H0.
  inversion H0; clear H0; subst.
  simpl in *.
  case_eq (f2 b); intros;
  rewrite H0 in H1.
  case_eq (combineOpt (List.map f2 l) ); intros;
  rewrite H4 in H1.
  inversion H1; clear H1; subst.
  erewrite H; eauto.
  rewrite H0.
  erewrite IHls1; eauto.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  
Qed.


Theorem combineOpt_map : forall (A B : Type)(f : A -> B) x y,
  combineOpt x = Some y ->
  combineOpt (map (fun z => match z with | Some a => Some (f a) | None => None end) x) = Some (map f y).

  induction x; intros; simpl in *.
  inversion H; clear H; subst.
  reflexivity.

  destruct a; simpl in *.
  case_eq (combineOpt x); intros.
  rewrite H0 in H.
  inversion H; clear H; subst.
  erewrite IHx; eauto.
  reflexivity.
  rewrite H0 in H.
  discriminate.
  discriminate.

Qed.

Theorem combineOpt_In_not_None : forall (A : Type)(ls : list (option A)) a y,
  combineOpt ls = Some y ->
  In a ls ->
  a <> None.

  induction ls; intros; simpl in *.
  intuition idtac.
  destruct a.
  intuition idtac.
  subst.
  discriminate.
  subst.
  case_eq (combineOpt ls); intros.
  rewrite H0 in H.
  inversion H; clear H; subst.
  eapply IHls.
  eauto.
  eauto.
  trivial.
  rewrite H0 in H.
  discriminate.
  discriminate.

Qed.

Theorem combineOpt_map_comm : forall (A : Type)(g : A -> A)(f : A -> option A) x y,
  (forall a b, f (g a) = Some b -> exists c, (f a) = Some c /\ (g c) = b) -> 
  combineOpt (map f (map g x)) = Some y ->
  exists z, combineOpt (map f x) = Some z /\ y = map g z.

  induction x; intros; simpl in *.
  inversion H0; clear H0; subst.
  exists nil. intuition idtac.
  case_eq (f (g a)); intros.
  rewrite H1 in H0.
  case_eq (combineOpt (map f (map g x))); intros.
  rewrite H2 in H0.
  inversion H0; clear H0; subst.
  edestruct IHx; eauto.
  intuition idtac.
  subst.
  edestruct H; eauto.
  intuition idtac; subst.
  rewrite H4.
  rewrite H3.
  econstructor.
  intuition idtac.
  rewrite H2 in H0.
  discriminate.
  rewrite H1 in H0.
  discriminate.
Qed.

Theorem multiSelect_cons : forall (A : Type)(x : list A) y1 y2,
  multiSelect x (y1 :: y2) = 
  match (nth_error x y1) with
  | Some y1' =>
    match (multiSelect x y2) with
    | Some y2' => Some (y1' :: y2')
    | None => None
    end
  | None => None
  end. 
  
  intros.
  reflexivity.

Qed.

Theorem multiSelect_app : forall (A : Type)(x : list A) y1 y2,
  multiSelect x (y1 ++ y2) = 
  match (multiSelect x y1) with
  | Some y1' => 
    match (multiSelect x y2) with 
    | Some y2' =>  Some (y1' ++ y2')
    | None => None
    end
  | None => None
   end.

  induction y1; intros; simpl in *.
  destruct (multiSelect x y2); trivial.
  repeat rewrite multiSelect_cons.
  rewrite IHy1.
  case_eq (nth_error x a); intros.
  case_eq (multiSelect x y1); intros.
  case_eq (multiSelect x y2); intros.
  simpl.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.

Qed.

Theorem combineOpt_length : forall (A : Type)(ls : list (option A)) x,
  combineOpt ls = Some x ->
  length ls = length x.

  induction ls; intros; simpl in *.
  inversion H; clear H; subst.
  trivial.
  destruct a.
  case_eq (combineOpt ls); intros;
  rewrite H0 in H.
  inversion H; clear H; subst.
  simpl.
  f_equal; eauto.
  discriminate.
  discriminate.

Qed.

Theorem multiSelect_length : forall (A : Type)(ls : list A) a b,
  multiSelect ls a = Some b ->
  length a = length b.

  intros.
  unfold multiSelect in *.
  apply combineOpt_length in H.
  rewrite map_length in H.
  trivial.

Qed.

Theorem combineOpt_map_flatten : 
  forall (A B : Type)(f : list A -> option (list B)) x x1,
  combineOpt (map f x) = Some x1 ->
  f nil = Some nil ->
  (forall a b y z, f a = Some y -> f b = Some z -> f (a ++ b) = Some (y ++ z)) -> 
  f (flatten x) = Some (flatten x1).

  induction x; intros; simpl in *.
  inversion H; clear H; subst.
  simpl.  
  trivial.

  case_eq (f a); intros;
  rewrite H2 in H.
  case_eq (combineOpt (map f x)); intros;
  rewrite H3 in H.
  inversion H; clear H; subst.
  simpl.
  erewrite H1.
  eauto.
  trivial.
  eapply IHx;
  eauto.
  
  discriminate.
  discriminate.

Qed.

Theorem combineOpt_f : forall (A B : Type)(f : A -> B) ls,
  combineOpt (List.map (fun x => Some (f x)) ls) = Some (List.map f ls).

  induction ls; intros; simpl in *.
  reflexivity.
  rewrite IHls.
  reflexivity.

Qed.

Definition stripOptLs(A : Type)(x: option (list A)) :=
  match x with
  | Some y => y
  | None => nil
  end. 

Theorem map_nth_error_Forall : forall l2  (A : Type)(l1 : list A) P,
  Forall P l1 ->
  Forall (fun x => match x with | Some y => P y | None => True end) (map (nth_error l1) l2).

  induction l2; intros; simpl in *.
  econstructor.
  econstructor; eauto.
  case_eq (nth_error l1 a); intros.
  eapply Forall_forall.
  eauto.
  eapply nth_error_In; eauto.
  apply I.

Qed.

Theorem Forall2_length : forall (A B : Type)(P : A -> B -> Prop) (lsa : list A) lsb,
    List.Forall2 P lsa lsb ->
    List.length lsa = List.length lsb.

    induction 1; intros; simpl in *.
    reflexivity.
    congruence.

Qed.

Theorem Forall_nth : forall (A : Type)(f : A -> Prop) ls n def,
  List.Forall f ls ->
  (n < List.length ls)%nat ->
  f (List.nth n ls def).

  induction ls; intros; simpl in *.
  destruct n; simpl in *; try lia.
  destruct n; simpl in *; try lia.  
  inversion H; clear H; subst.
  trivial.
  inversion H; clear H; subst.
  eapply IHls.
  eauto.
  lia.
  
Qed.

Theorem Forall2_map_l : forall (A B C: Type) P (f : A -> C) lsa (lsb : list B),
  List.Forall2 (fun x y => P (f x) y) lsa lsb ->
  List.Forall2 P (List.map f lsa) lsb.

  induction 1; intros; simpl in *.
  econstructor.
  econstructor; eauto.

Qed.

Theorem Forall2_map_r : forall (A B C: Type) P (f : B -> C) (lsa : list A) lsb,
  List.Forall2 (fun x y => P x (f y)) lsa lsb ->
  List.Forall2 P lsa (List.map f lsb).

  induction 1; intros; simpl in *.
  econstructor.
  econstructor; eauto.

Qed.


Theorem Forall2_same_Forall : forall (A : Type) P (ls : list A),
  List.Forall (fun x => P x x) ls ->
  List.Forall2 P ls ls.

  induction 1; intros; simpl in *.
  econstructor.
  econstructor; eauto.

Qed.

Theorem Forall_I : forall (A : Type)(ls : list A),
  List.Forall (fun x => True) ls.

  induction ls; intuition idtac; econstructor; eauto.

Qed.

Theorem Foralll2_impl : forall (A B : Type)(P1 P2 : A -> B -> Prop) ls1 ls2,
  List.Forall2 P1 ls1 ls2 ->
  (forall a b, List.In a ls1 -> List.In b ls2 -> P1 a b -> P2 a b) ->
  List.Forall2 P2 ls1 ls2.

  induction 1; intros; simpl in *.
  econstructor.
  econstructor.
  eauto.
  eauto.

Qed.

Theorem Forall_flatten : forall (A : Type)(P : A -> Prop) (ls : list (list A)),
  (forall x, List.In x ls -> List.Forall P x) ->
  List.Forall P (flatten ls).

  induction ls; intros; simpl in *.
  econstructor.
  eapply Forall_app.
  intuition idtac.
  eapply H; intuition idtac.
  eapply IHls; intuition idtac.
  eapply H; intuition idtac.

Qed.

Theorem Forall2_Forall_impl : forall (A B : Type)(lsa : list A)(lsb : list B) (P1: A -> B -> Prop) (P2 : A -> Prop),
  List.Forall2 P1 lsa lsb ->
  (forall a b, P1 a b -> P2 a) ->
  List.Forall P2 lsa.

  induction lsa; intros; simpl in *.
  inversion H; clear H; subst.
  econstructor.

  inversion H; clear H; subst.
  econstructor.
  eauto.
  eauto.

Qed.

Theorem Forall_Forall2_impl: forall (A B : Type)(lsa : list A)(lsb : list B) (P2 : A -> Prop),
  List.Forall P2 lsa -> 
  (List.length lsb = List.length lsa) ->
  List.Forall2 (fun a b => P2 a) lsa lsb.

  induction lsa; intros; simpl in *.
  destruct lsb; simpl in *; try lia.
  econstructor.

  inversion H; clear H; subst.
  destruct lsb; simpl in *; try lia.
  econstructor; eauto.

Qed.

Theorem Forall2_impl_2 : forall (A B : Type)(P1 P2 : A -> B -> Prop) lsa lsb,
  List.Forall2 P1 lsa lsb ->
  List.Forall2 P2 lsa lsb ->
  List.Forall2 (fun a b => P1 a b /\ P2 a b) lsa lsb.

  induction 1; intros; simpl in *.
  inversion H; clear H; subst.
  econstructor.
  inversion H1; clear H1; subst.
  econstructor.
  intuition idtac.
  eauto.
Qed.

Theorem combineOpt_In : forall (A : Type)(ls :list (option A)) ls' x,
  combineOpt ls = Some ls' -> 
  List.In x ls' -> 
  List.In (Some x) ls.

  induction ls; intros; simpl in *.
  optSomeInv.
  simpl in *.
  intuition idtac.

  optSomeInv.
  simpl in *.
  intuition idtac; subst.
  left; eauto.
  right.
  eauto.

Qed.

Theorem multiSelect_In : forall (A : Type)(ls1 : list A) ls2 x y, 
  multiSelect ls1 x = Some ls2 ->
  List.In y ls2 -> List.In y ls1.

  intros.
  unfold multiSelect in *.
  eapply combineOpt_In in H; eauto.
  apply in_map_iff in H.
  destruct H.
  intuition idtac; simpl in *.
  apply nth_error_In in H1.
  trivial.

Qed.

Theorem In_tl : forall (A : Type)(ls : list A) a,
  List.In a (List.tl ls) ->
  List.In a ls.

  intros.
  destruct ls; simpl in *.
  intuition idtac.
  intuition idtac.

Qed.

Theorem hd_In : forall (A : Type)(ls : list A)(a : A),
  ls <> List.nil ->
  List.In (List.hd a ls) ls.

  intros.
  destruct ls.
  intuition idtac.
  simpl.
  intuition idtac.

Qed.

Theorem nth_error_map_ex : forall (A B : Type)(f : A -> B) ls x n,
  nth_error (List.map f ls) n = Some x ->
  exists y, nth_error ls n = Some y /\ x = f y.

  induction ls; destruct n; intros; simpl in *; try discriminate.
  inversion H; clear H; subst.
  econstructor; intuition idtac.
  eapply IHls; eauto.

Qed.

Theorem combineOpt_map_Some : forall (A B : Type)(f : A -> option B) (x : list A)(pa : A -> Prop)(pb : A -> B -> Prop),
  List.Forall pa x -> 
  (forall a, pa a -> exists b, f a = Some b /\ pb a b) -> 
  exists y, combineOpt (List.map f x) = Some y /\ List.Forall2 pb x y.

  induction x; intros; simpl in *.
  exists List.nil.
  intuition idtac.
  econstructor.

  inversion H; clear H; subst.
  edestruct (H0 a); eauto.
  intuition idtac.
  rewrite H1.
  edestruct IHx; intuition idtac.
  eauto.
  edestruct (H0 a0); intuition idtac.
  exists x1; intuition idtac.
  eauto.
  rewrite H5.
  econstructor; intuition idtac.
  econstructor; intuition idtac.    

Qed.

Theorem combineOpt_Some : forall (A : Type)(ls : list (option A)) x,
  combineOpt ls = Some x ->
  List.Forall2 (fun x y => x = Some y) ls x.

  induction ls; intros; simpl in *; optSomeInv.
  econstructor.

  econstructor.
  trivial.
  eauto.

Qed.

Theorem nth_error_Some_ex : forall (A : Type)n (ls : list A),
  (n < List.length ls)%nat ->
  exists y,
    nth_error ls n = Some y.

  induction n; destruct ls; intros; simpl in *; try lia.
  econstructor; eauto.
  edestruct IHn; eauto. lia. 

Qed.

Require Import Vector.
Local Arguments Vector.cons [_] h [_] t.

Fixpoint vecRepeat(A : Type)(a : A)(n : nat) : Vector.t A n :=
  match n with
  | O =>@Vector.nil A
  | S n' => Vector.cons a (vecRepeat a n')
  end.

Theorem bvector_eq_dec : forall n (v1 v2 : VectorDef.t bool n),
  {v1 = v2} + {v1 <> v2}.

  intros.
  apply (Vector.eq_dec _ Bool.eqb).
  intros.
  apply Bool.eqb_true_iff.

Defined.

