
Require Import ZArith.
Require Import ZArith.BinInt.
Require Import micromega.Lia.

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