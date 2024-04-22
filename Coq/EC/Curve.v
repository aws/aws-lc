(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0 *)

From Coq Require Import Ring.
From Coq Require Import ZArith.BinInt.
From Coq Require Import Lia.
From Coq Require Import Classes.SetoidClass.
From Coq Require Import Setoid.

From Crypto Require Import Algebra.Hierarchy.
From Crypto Require Import Algebra.Field.
From Crypto Require Import Algebra.Nsatz.
From Crypto Require Import Curves.Weierstrass.Jacobian.
From Crypto Require Import Curves.Weierstrass.Affine.

From Crypto Require Import Curves.Weierstrass.AffineProofs.

From EC Require Import Util.
From EC Require Import CommutativeGroup.

Fixpoint Fpow `{field} n x :=
  match n with
  | O => one
  | S n' => mul x (Fpow n' x)
  end.

(* An elliptic curve over a field with some additional restrictions *)
Class Curve
  (F : Type)(Feq: F -> F -> Prop)
  {Fzero Fone : F}
  {Fadd Fsub Fmul Fdiv : F -> F -> F}
  {Fopp Finv : F -> F}
  `{F_field : field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
  {a b : F}
:=
{
  (* The "a" coefficient is -3, as is the case for NIST prime curves *)
  a_is_minus_3 : Feq a (Fopp (Fadd (Fadd Fone Fone) Fone));
  (* Field has characteristic at least 28 enables a simple proof that the discriminant is nonzero. *)
  Fchar_28 : @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 28;
  (* Discriminant is non-zero follows from a=-3 and b<>2 and b<>-2 when characteristic is large*)
  b_ne_plus_minus_2 : 
    ~((Feq b (Fadd Fone Fone)) \/ (Feq b (Fopp (Fadd Fone Fone))))
}.

(* The field must have characteristic at least 12 in order for the base point to generate a group. *)
Global Instance Fchar_12 : forall `{Curve}, @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 12.
  intros.
  eapply char_ge_weaken.
  apply Fchar_28.
  lia.

Defined.

(* Point addition requires the field to have characteristic at least 3. *)
Global Instance Fchar_3 : forall `{Curve}, @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 3.

  intros.
  eapply char_ge_weaken.
  apply Fchar_12.
  lia.

Qed.

Definition point `{Curve}{Feq_dec : DecidableRel Feq} : Type := @Jacobian.point F Feq Fzero Fadd Fmul a b Feq_dec.
Definition double_minus_3 `{Curve}{Feq_dec : DecidableRel Feq}  := @Jacobian.double_minus_3 F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b F_field Feq_dec a_is_minus_3.
Definition double `{Curve}{Feq_dec : DecidableRel Feq}  := @Jacobian.double F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b F_field Feq_dec.
Definition add `{Curve}{Feq_dec : DecidableRel Feq}  := @Jacobian.add F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b F_field Fchar_3 Feq_dec.
Definition to_affine `{Curve}{Feq_dec : DecidableRel Feq}  := @Jacobian.to_affine F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b F_field Feq_dec.

Definition jac_eq`{Curve}{Feq_dec : DecidableRel Feq} (p1 p2 : F * F * F) :=
  let '(X1, Y1, Z1) := p1 in
  let '(X2, Y2, Z2) := p2 in
    if dec (Feq Z1 Fzero)
    then Feq Z2 Fzero
    else
     ~ Feq Z2 Fzero /\
     Feq (Fmul X1 (Fmul Z2 Z2)) (Fmul X2 (Fmul Z1 Z1)) /\
     Feq (Fmul Y1 (Fmul (Fmul Z2 Z2) Z2)) (Fmul Y2 (Fmul (Fmul Z1 Z1) Z1)).

Definition opp `{Curve}{Feq_dec : DecidableRel Feq} : point -> point := Jacobian.opp.

Definition is_jacobian `{Curve}{Feq_dec : DecidableRel Feq} (p : F * F * F) :=
  let '(X, Y, Z) := p in
  if dec (Feq Z Fzero)
    then True
    else
     Feq (Fmul Y Y)
       (Fadd
          (Fadd (Fmul (Fmul X X) X)
             (Fmul 
                (Fmul a X)
                (Fmul 
                 (Fmul Z Z) 
                 (Fmul Z Z))))
          (Fmul b
             (Fmul 
                (Fmul (Fmul Z Z) Z)
                (Fmul (Fmul Z Z) Z)))).

Definition affine_point `{Curve} := Vector.t F 2.
Definition affine_point_prod `{Curve} := (F * F)%type.

Definition on_curve `{Curve}(p : affine_point ) : Prop :=
    let x := Vector.nth_order p zero_lt_two in
    let y := Vector.nth_order p one_lt_two in 
    Feq (Fmul y y) (Fadd (Fmul x (Fmul x x)) (Fadd (Fmul a x) b)).

Definition affine_point_alg`{Curve}{Feq_dec : DecidableRel Feq}  := @WeierstrassCurve.W.point F Feq Fadd Fmul a b.

Definition fromAffinePoint`{Curve}{Feq_dec : DecidableRel Feq} (p:affine_point_alg) : option affine_point_prod :=
  match (proj1_sig p) with
  | inl (x, y) => Some (x, y)
  | inr _ => None
  end.


Definition fromPoint `{Curve}{Feq_dec : DecidableRel Feq} (p:point) : (F*F*F) :=
  proj1_sig p.

Definition prodToSeq`{Curve}{Feq_dec : DecidableRel Feq} (p : F * F * F) : Vector.t F 3 :=
  Vector.cons _ (fst (fst p)) _ (Vector.cons _ (snd (fst p)) _ (Vector.cons _ (snd p) _ (@Vector.nil F))).

Definition seqToProd`{Curve}{Feq_dec : DecidableRel Feq} (p : Vector.t F 3) : F * F * F :=
  (Vector.nth_order p zero_lt_three, Vector.nth_order p one_lt_three, Vector.nth_order p two_lt_three).

Definition toPoint`{Curve}{Feq_dec : DecidableRel Feq} (p : F * F * F)(pf : is_jacobian p) : point :=
  exist _ p pf.

Definition zero_point_h`{Curve} : F * F * F := (Fzero, Fone, Fzero).
Theorem zero_point_is_jacobian : forall `{Curve}{Feq_dec : DecidableRel Feq} , is_jacobian zero_point_h.

  intros.
  unfold is_jacobian, zero_point_h.
  destruct (dec (Feq Fzero Fzero)); intuition.
  exfalso.
  eapply n.
  nsatz.

Qed.

Definition zero_point`{Curve}{Feq_dec : DecidableRel Feq}  : point :=
  exist _  zero_point_h zero_point_is_jacobian.

(* Weierstrass curve is used to produce commutative group *)
Definition wpoint`{Curve} := @WeierstrassCurve.W.point F Feq Fadd Fmul a b.
Definition W_opp`{Curve}{Feq_dec : DecidableRel Feq}  : wpoint -> wpoint := W.opp.
Definition W_eq`{Curve} : wpoint -> wpoint -> Prop := WeierstrassCurve.W.eq.
Definition W_add`{Curve}{Feq_dec : DecidableRel Feq}  : wpoint -> wpoint -> wpoint := WeierstrassCurve.W.add.
Definition wzero`{Curve} : wpoint := WeierstrassCurve.W.zero.

Section DiscriminantNonzero.

  Context `{curve: Curve}.
  Context {Feq_dec : DecidableRel Feq}.

  Local Notation "0" := Fzero.  Local Notation "1" := Fone.
  Local Infix "+" := Fadd. Local Infix "-" := Fsub.
  Local Infix "*" := Fmul. Local Infix "/" := Fdiv.
  Local Notation "x ^ 2" := (x*x) (at level 30).
  Local Notation "x ^ 3" := (x^2*x) (at level 30).

    
  Theorem discriminant_nonzero : 
    ~
  Feq
  ((1 + 1 + 1 + 1) * a * a * a +
   ((1 + 1 + 1 + 1) ^ 2 + (1 + 1 + 1 + 1) + (1 + 1 + 1 + 1) + 1 + 1 + 1) * b * b) 0.

    intros.
    repeat rewrite a_is_minus_3.

    assert (Feq ((1 + 1 + 1 + 1) * Fopp (1 + 1 + 1) * Fopp (1 + 1 + 1) * Fopp (1 + 1 + 1)) (((1 + 1 + 1)^3) * (Fopp (1 + 1 + 1 + 1)))).
    nsatz.
    rewrite H.
    assert (Feq  (((1 + 1 + 1 + 1) ^ 2 + (1 + 1 + 1 + 1) + (1 + 1 + 1 + 1) + 1 + 1 + 1) * b * b) (((1 + 1 + 1)^3) * (b^2))).
    nsatz.
    rewrite H0.
    unfold Logic.not.
    intros.

    assert (~ Feq (1 + (1 + 1) * (1 + (1 + 1) * ((1 + 1) * (1 + (1 + 1))))) 0).
    assert (Feq (1 + (1 + 1) * (1 + (1 + 1) * ((1 + 1) * (1 + (1 + 1))))) (@Ring.of_Z F 0 1 Fopp Fadd  (Z.pos 27))).
    simpl.
    nsatz.
    rewrite H2.

    eapply Fchar_28.
    lia.

    assert (Feq ((b + (1 + 1)) * (b  + (Fopp (1 + 1)))) 0).
    nsatz.
    destruct (dec (Feq b (1+1))).
    apply b_ne_plus_minus_2.
    left.
    trivial.
    apply b_ne_plus_minus_2.
    right.
    assert (Feq ((b + (1 + 1)) * ((Finv (b + Fopp (1 + 1)))* ( (b + Fopp (1 + 1))))) 0).
    nsatz.
    rewrite left_multiplicative_inverse in H4.
    nsatz.
    intuition idtac.
    eapply n.
    nsatz.

  Qed.
End DiscriminantNonzero.

Global Instance W_commutative_group : 
  forall `{Curve}{Feq_dec : DecidableRel Feq},
  @commutative_group wpoint
  WeierstrassCurve.W.eq
  WeierstrassCurve.W.add
  WeierstrassCurve.W.zero
  W.opp.

  intros.
  apply W.commutative_group.
  apply Fchar_12.
  unfold Datatypes.id.
  apply discriminant_nonzero.  

Defined.

Global Instance jac_eq_setoid : forall `{Curve}{Feq_dec : DecidableRel Feq}, Setoid point := {equiv := Jacobian.eq}.
Global Instance w_eq_setoid : forall `{Curve}{Feq_dec : DecidableRel Feq}, Setoid wpoint := {equiv := WeierstrassCurve.W.eq}.


Section CurveFacts.

  Context `{curve : Curve}.
  Context {Feq_dec : DecidableRel Feq}.

  Local Notation "0" := Fzero.  Local Notation "1" := Fone.
  Local Infix "+" := Fadd. Local Infix "-" := Fsub.
  Local Infix "*" := Fmul. Local Infix "/" := Fdiv.
  Local Notation "x ^ 2" := (x*x) (at level 30).
  Local Notation "x ^ 3" := (x^2*x) (at level 30).

  (* Additional field facts *)
  Theorem fmul_same_r : forall x v1 v2,
    Feq v1 v2 ->
    Feq (v1 * x) (v2 * x).

    intros.
    rewrite H.
    reflexivity.
  Qed.

  Theorem fadd_same_r : forall x v1 v2,
    Feq v1 v2 ->
    Feq (v1 + x) (v2 + x).

    intros.
    rewrite H.
    reflexivity.
  Qed.

  Theorem f_zero_absorb : forall (x : F),
    Feq (x * 0) 0.

    intros.
    symmetry.
    rewrite <- (right_identity (x * 0)).
    rewrite <- (right_inverse (x * 0)) at 1.
    rewrite <- (right_inverse (x * 0)) at 4.
    rewrite (associative (x * 0)).
    apply fadd_same_r.
    rewrite <- left_distributive.
    rewrite right_identity.
    reflexivity.

  Qed.

  Theorem square_nz : forall (x : F),
    ~(Feq x 0) ->
    ~(Feq (x ^ 2 ) 0).

    intuition idtac.
    eapply (@fmul_same_r (Finv x)) in H0.
    rewrite <- (associative x) in H0.
    rewrite (commutative _ (Finv x)) in H0.
    rewrite left_multiplicative_inverse in H0.
    rewrite right_identity in H0.
    rewrite (commutative 0) in H0.
    rewrite f_zero_absorb in H0.
    intuition idtac.
    intuition idtac.

  Qed.

  Theorem cube_nz : forall (x : F),
    ~(Feq x 0) ->
    ~(Feq (x ^ 3) 0).

    intuition idtac.
    eapply (@fmul_same_r (Finv x)) in H0.
    rewrite <- (associative x) in H0.
    rewrite (commutative _ (Finv x)) in H0.
    rewrite (associative (Finv x)) in H0.
    rewrite left_multiplicative_inverse in H0.
    rewrite left_identity in H0.
    rewrite (commutative 0) in H0.
    rewrite f_zero_absorb in H0.

    eapply (@fmul_same_r (Finv x)) in H0.
    rewrite <- (associative x) in H0.
    rewrite (commutative _ (Finv x)) in H0.
    rewrite left_multiplicative_inverse in H0.
    rewrite right_identity in H0.
    rewrite (commutative 0) in H0.
    rewrite f_zero_absorb in H0.
    intuition idtac.
    intuition idtac.
    intuition idtac.

  Qed.

  Theorem square_mul_eq : forall (x y : F),
    Feq ((x * y)^2) (x^2 * y^2).
  
    intros.
    repeat rewrite associative.
    apply ring_mul_Proper.
    rewrite <- (associative x x).  
    rewrite <- associative.
    apply ring_mul_Proper.
    reflexivity.
    apply commutative.
    reflexivity.
  Qed.

  Theorem cube_mul_eq : forall (x y : F),
    Feq ((x * y)^3) (x^3 * y^3).

    intros.
    rewrite square_mul_eq.
    repeat rewrite <- (associative (x^2)).
    apply ring_mul_Proper.
    reflexivity.
    rewrite (commutative x (y^3)).
    rewrite <- (associative (y^2)).
    apply ring_mul_Proper.
    reflexivity.
    apply commutative.
  Qed.

  
  Theorem fmul_same_r_if : forall (x y z : F),
    ~ (Feq x 0) ->
    Feq (y * x) (z * x) ->
    Feq y z.

    intros.
    eapply (fmul_same_r (Finv x)) in H0.
    rewrite <- associative in H0.
    rewrite (commutative x) in H0.
    rewrite left_multiplicative_inverse in H0.
    rewrite right_identity in H0.
    rewrite <- associative in H0.
    rewrite (commutative x) in H0.
    rewrite left_multiplicative_inverse in H0.
    rewrite right_identity in H0.
    trivial.
    trivial.
    trivial.

  Qed.

  Theorem fadd_same_r_if : forall (x y z : F),
    Feq (y + x) (z + x) ->
    Feq y z.

    intros.
    eapply (fadd_same_r (Fopp x)) in H.
    rewrite <- associative in H.
    rewrite (commutative x) in H.
    rewrite left_inverse in H.
    rewrite right_identity in H.
    rewrite <- associative in H.
    rewrite (commutative x) in H.
    rewrite left_inverse in H.
    rewrite right_identity in H.
    trivial.

  Qed.

  Theorem mul_nz : forall (x y : F),
    ~(Feq x 0) ->
    ~(Feq y 0) ->
    ~(Feq (x * y) 0).

    intuition idtac.
    
    eapply (@fmul_same_r (Finv y)) in H1.
    rewrite <- (associative x) in H1.
    rewrite (commutative _ (Finv y)) in H1.
    rewrite left_multiplicative_inverse in H1.
    rewrite right_identity in H1.
    rewrite (commutative 0) in H1.
    rewrite f_zero_absorb in H1.
    intuition idtac.
    intuition idtac.

  Qed.

  Theorem mul_nz_if : forall x y,
    ~ Feq x 0 ->
    ~ Feq y 0 -> 
    ~Feq (x * y) 0.

    intros.
    intuition idtac.
    assert (Feq ((Finv x) * (x * y)) ((Finv x) * 0)).
    rewrite H1.
    reflexivity.
    rewrite associative in H2.
    rewrite left_multiplicative_inverse in H2.
    rewrite left_identity in H2.
    subst.
    apply H0.
    nsatz.
    trivial.
  Qed.

  Theorem inv_mul_eq : forall (x y : F),
    ~(Feq y 0) ->
    ~(Feq x 0) ->
    Feq (Finv (x*y)) ((Finv x) * (Finv y)).

    intros.
    eapply (@fmul_same_r_if y).
    trivial.
    rewrite <- associative.
    rewrite left_multiplicative_inverse; trivial.
    rewrite right_identity.
    
    eapply (@fmul_same_r_if x).
    trivial.
    rewrite left_multiplicative_inverse; trivial.
    rewrite <- associative.
    rewrite (commutative y).
    apply left_multiplicative_inverse.
    apply mul_nz; eauto.
 
  Qed.

  Theorem inv_square_eq : forall (x : F),
    ~(Feq x 0) ->
    Feq ((Finv x)^2) (Finv (x^2)).

    symmetry.
    apply inv_mul_eq; eauto.

  Qed.

  Theorem inv_cube_eq : forall (x : F),
    ~(Feq x 0) ->
    Feq ((Finv x)^3) (Finv (x^3)).

    symmetry.
    rewrite inv_mul_eq; eauto.
    rewrite inv_square_eq; eauto.
    reflexivity.
    apply square_nz; trivial.

  Qed.

  Theorem cube_square_eq : forall (x : F),
    Feq ((x^3)^2) ((x^2)^3).

    intros.
    repeat rewrite associative.
    reflexivity.

  Qed.

  Theorem opp_mul_eq : forall (x : F),
    Feq (Fopp x) (Fmul (Fopp 1) x).

    intros.
    eapply (@fadd_same_r_if x).
    rewrite left_inverse.
    assert (Feq x (1 * x)).
    nsatz.
    rewrite H at 2.
    rewrite <- right_distributive.
    rewrite left_inverse.
    symmetry.
    rewrite commutative.
    apply f_zero_absorb.

  Qed.

  Theorem fmul_same_l:
    forall [x y z : F],
    Feq y z ->
    Feq (x * y) (x * z).

    intros.
    rewrite H.
    reflexivity.
  Qed.

  Theorem Fsub_0_eq : forall a0 b0,
    Feq (a0 - b0) 0 ->
    Feq a0 b0.

    intros.
    nsatz.

  Qed.

  Theorem Fsub_not_0_neq : forall a0 b0,
    ~(Feq (a0 - b0) 0) ->
    ~(Feq a0 b0).

    intros.
    intuition idtac.
    eapply H.
    nsatz.

  Qed.

  Theorem Fzero_ne_Fone:
    ~(Feq Fzero Fone).

    intros.
    eapply zero_neq_one.

  Qed.

  Theorem Fone_ne_Fzero:
    ~(Feq Fone Fzero).

    intuition idtac.
    apply Fzero_ne_Fone.
    symmetry.
    eauto.

  Qed.

  Theorem Fpow_0 : forall n,
    n <> O ->
    Feq (Fpow n 0) 0.

    destruct n; intros; simpl in *.
    intuition idtac.
    nsatz.

  Qed.

  Theorem Fpow_minus_1_div : forall n x,
    n <> 0%nat -> 
    ~(Feq x 0) -> 
    Feq (Fpow (n - 1) x) (Fdiv (Fpow n x) x).
  
    intros.
    
    destruct n.
    lia.
    simpl.
    replace (n - 0)%nat with n.
    rewrite field_div_definition.
    rewrite <- associative.
    rewrite commutative.
    rewrite <- associative.
    rewrite left_multiplicative_inverse.
    nsatz.
    intuition idtac.
    lia.
  Qed.

  Theorem Fmul_same_l : forall z x y,
    ~(Feq z 0) -> 
    Feq (z * x) (z * y) ->
    Feq x y.

    intros.
    assert (Feq ((Finv z) * (z * x)) ((Finv z) * (z * y))).
    rewrite H0.
    reflexivity.
    rewrite associative in H1.
    rewrite left_multiplicative_inverse in H1.
    rewrite left_identity in H1.
    rewrite H1.
    rewrite associative.
    rewrite left_multiplicative_inverse.
    nsatz.
    trivial.
    trivial.

  Qed.

  Theorem Fmul_nz : forall x y,
    ~Feq x 0 ->
    ~Feq y 0 -> 
    ~Feq (x * y) 0.

    intros.
    intuition idtac.
    assert (Feq ((Finv x) * (x * y))  ((Finv x) * 0)).
    rewrite H1.
    reflexivity.
    rewrite associative in H2.
    rewrite left_multiplicative_inverse in H2.
    rewrite left_identity in H2.
    apply H0.
    nsatz.
    trivial.
  Qed.

  Theorem Fpow_nz : forall n x,
    ~Feq x 0 ->
    ~Feq (Fpow n x) 0.

    induction n; intros; simpl in *.
    assert (~ Feq 0 1).
    apply zero_neq_one.
    intuition idtac.
    apply H0.
    symmetry.
    trivial.
    apply Fmul_nz; eauto.
  Qed.

  Theorem Finv_1 :
    Feq (Finv 1) 1.

    apply (Fmul_same_l 1).
    assert (~Feq 0 1).
    apply zero_neq_one.
    intuition idtac.
    apply H.
    symmetry.
    trivial.
    rewrite commutative.
    rewrite left_multiplicative_inverse.
    rewrite left_identity.
    reflexivity.
    assert (~Feq 0 1).
    apply zero_neq_one.
    intuition idtac.
    apply H.
    symmetry.
    trivial.
  Qed.


  Theorem Fpow_minus_div : forall n2 n1 x,
    n1 >= n2 -> 
    ~Feq x 0 -> 
    Feq (Fpow (n1 - n2) x) (Fdiv (Fpow n1 x) (Fpow n2 x)).
  
    induction n2; intros; simpl.
    replace (n1 - 0)%nat with n1.
    rewrite field_div_definition.
    rewrite commutative.
    rewrite Finv_1.
    nsatz.
    lia.

    destruct n1.
    lia.
    simpl.
    rewrite IHn2.
    rewrite field_div_definition.
    rewrite field_div_definition.
    rewrite inv_mul_eq.
    setoid_replace ( x * Fpow n1 x * (Finv x * Finv (Fpow n2 x))) with ( ((Finv x) * x) * Fpow n1 x * (Finv (Fpow n2 x))).
    rewrite left_multiplicative_inverse.
    nsatz.
    intuition idtac.
    nsatz.
    trivial.
    apply Fpow_nz; eauto.
    trivial.
    lia.
    trivial.
 
  Qed.

  Theorem Fpow_add: forall x y z,
    Feq (Fpow (x + y) z) ((Fpow x z) * (Fpow y z)).

    induction x; intros; simpl.
    rewrite left_identity.
    reflexivity.

    rewrite IHx.
    rewrite associative.
    reflexivity.

  Qed.

  Theorem Fpow_mul : forall x y z,
    Feq (Fpow (x * y) z) ((Fpow x (Fpow y z))).

    induction x; intros; simpl.
    reflexivity.
    rewrite Fpow_add.
    rewrite IHx.
    reflexivity.
  Qed.

  (* Facts about jac_eq *)
  Theorem jac_eq_refl : forall p, jac_eq p p.

    intros.
    unfold jac_eq.
    destruct p.
    destruct p.
    destruct (dec (Feq f 0)).
    trivial.
    intuition idtac.
    reflexivity.
    reflexivity.
  Qed.

  Theorem jac_eq_refl_abstract : forall p1 p2,
    p1 = p2 ->
    jac_eq p1 p2.

    intros.
    rewrite H.
    apply jac_eq_refl.

  Qed.

  Theorem jac_eq_trans : forall p1 p2 p3,
    jac_eq p1 p2 ->
    jac_eq p2 p3 ->
    jac_eq p1 p3.

    intros.
    unfold jac_eq in *.
    destruct p1. destruct p. destruct p2. destruct p.
    destruct p3. destruct p.
    destruct (dec (Feq f 0)).
    destruct (dec (Feq f2 0));
    intuition idtac.
    destruct (dec (Feq f2 0)); intuition idtac.

    eapply (fmul_same_r (Finv (f^2))) in H0.
    rewrite <- (associative f3) in H0.
    rewrite (commutative (f^2)) in H0.
    rewrite left_multiplicative_inverse in H0.
    rewrite right_identity in H0.
    rewrite <- H0 in H2.
    eapply (fmul_same_r (Finv (f2^2))) in H2.
    rewrite <- (associative f6) in H2.
    rewrite (commutative (f2^2)) in H2.
    rewrite left_multiplicative_inverse in H2.
    rewrite right_identity in H2.
    rewrite (commutative _ (Finv (f2^2))) in H2.
    rewrite (commutative f0) in H2.
    do 3 rewrite (associative (Finv (f2^2))) in H2.    
    rewrite left_multiplicative_inverse in H2.
    rewrite left_identity in H2.
    eapply (fmul_same_r (f^2)) in H2.
    rewrite (commutative _ (f^2)) in H2.
    rewrite (commutative f0) in H2.
    do 2 rewrite (associative (f^2)) in H2.
    rewrite (commutative (f^2)) in H2.
    rewrite left_multiplicative_inverse in H2.
    rewrite left_identity in H2.
    trivial.

    eapply square_nz; eauto with typeclass_instances; intuition idtac.
    eapply square_nz; eauto with typeclass_instances; intuition idtac.
    eapply square_nz; eauto with typeclass_instances; intuition idtac.
    eapply square_nz; eauto with typeclass_instances; intuition idtac.
    
    eapply (fmul_same_r (Finv (f^3))) in H4.
    rewrite <- (associative f4) in H4.
    rewrite (commutative (f^3)) in H4.
    rewrite left_multiplicative_inverse in H4.
    rewrite right_identity in H4.
    rewrite <- H4 in H5.
    eapply (fmul_same_r (Finv (f2^3))) in H5.
    rewrite <- (associative f7) in H5.
    rewrite (commutative (f2^3)) in H5.
    rewrite left_multiplicative_inverse in H5.
    rewrite right_identity in H5.
    rewrite (commutative _ (Finv (f2^3))) in H5.
    rewrite (commutative f1) in H5.
    do 3 rewrite (associative (Finv (f2^3))) in H5.    
    rewrite left_multiplicative_inverse in H5.
    rewrite left_identity in H5.
    eapply (fmul_same_r (f^3)) in H5.
    rewrite (commutative _ (f^3)) in H5.
    rewrite (commutative f1) in H5.
    do 2 rewrite (associative (f^3)) in H5.
    rewrite (commutative (f^3)) in H5.
    rewrite left_multiplicative_inverse in H5.
    rewrite left_identity in H5.
    trivial.
    
    eapply cube_nz; eauto with typeclass_instances; intuition idtac.
    eapply cube_nz; eauto with typeclass_instances; intuition idtac.
    eapply cube_nz; eauto with typeclass_instances; intuition idtac.
    eapply cube_nz; eauto with typeclass_instances; intuition idtac.

  Qed.
  
  Theorem jac_eq_symm : forall p1 p2,
    jac_eq p1 p2 ->
    jac_eq p2 p1.

    intros. 
    unfold jac_eq in *.
    destruct p1. destruct p.
    destruct p2. destruct p.
    destruct (dec (Feq f 0)).
    destruct (dec (Feq f2 0));
    intuition idtac.
    destruct (dec (Feq f2 0)); 
    intuition idtac.
    symmetry.
    trivial.
    symmetry.
    trivial.
  Qed.

  Theorem jacobian_eq_jac_eq : forall p1 p2,
    Jacobian.eq p1 p2 ->
    jac_eq (fromPoint p1) (fromPoint p2).

    intros.
    unfold jac_eq, fromPoint, Jacobian.eq in *.
    apply H.

  Qed.


  Theorem double_minus_3_eq_double : forall P,
      Jacobian.eq (double P) (double_minus_3 P).

    intros.
    eapply Jacobian.double_minus_3_eq_double.
  Qed.

  Theorem to_affine_add: forall `{Curve}`{DecidableRel Feq} P Q,
    W_eq (to_affine (add P Q)) (W_add (to_affine P) (to_affine Q)).

    intros.
    apply Jacobian.to_affine_add.

  Qed.

  Theorem jac_eq_from_affine : forall (x y : point),
    W_eq (to_affine x) (to_affine y) ->
    x == y.
  
    intros.
    rewrite <- Jacobian.of_affine_to_affine.
    symmetry.
    rewrite <- Jacobian.of_affine_to_affine.
    symmetry.
    apply Jacobian.Proper_of_affine.
    trivial.
  Qed.

  Theorem jac_add_assoc : forall (x y z : point),
    Jacobian.eq (add (add x y) z) (add x (add y z)).

    intros.
    apply jac_eq_from_affine.
    repeat rewrite to_affine_add.
    rewrite associative.
    reflexivity.

  Qed.

  Theorem jac_add_comm : forall (a b : point),
    Jacobian.eq (add a b) (add b a).

    intros.
    apply jac_eq_from_affine.
    repeat rewrite to_affine_add.
    apply commutative.

  Qed.

  Theorem to_affine_zero : W_eq (to_affine zero_point) WeierstrassCurve.W.zero.

    unfold W_eq, WeierstrassCurve.W.eq, to_affine, Jacobian.to_affine, zero_point.
    simpl.
    destruct (dec (Feq 0 0)); trivial.
    intuition idtac.
    eapply n.
    reflexivity.
  Qed.

  Theorem jac_add_id_l : forall (a : point),
    Jacobian.eq (add zero_point a)  a.

    intros.
    apply jac_eq_from_affine.
    rewrite to_affine_add.
    rewrite to_affine_zero.  
    apply left_identity.

  Qed.

  Theorem jac_double_correct : forall (a : point),
    Jacobian.eq (double a) (add a a).

    intros.
    apply jac_eq_from_affine.
    rewrite to_affine_add.
    unfold double, to_affine.
    rewrite Jacobian.to_affine_double.
    reflexivity.

  Qed.

  Theorem Proper_opp : Proper (Jacobian.eq ==> Jacobian.eq) opp.
  
    intros.
    unfold Proper, respectful, Jacobian.eq, Jacobian.opp.
    intros.
    simpl in *.
    destruct (proj1_sig x). destruct p.
    destruct (proj1_sig y). destruct p.
    destruct (dec (Feq f 0)).
    trivial.
    intuition idtac.
    rewrite opp_mul_eq.
    rewrite (opp_mul_eq f4).
    repeat rewrite <- (associative (Fopp 1)).
    eapply fmul_same_l; eauto.
  Qed.

  Theorem to_affine_opp : forall x, 
    W_eq (to_affine (opp x)) (W_opp (to_affine x)).

    intros.

    unfold W_eq, WeierstrassCurve.W.eq, to_affine, Jacobian.to_affine, Jacobian.opp, W_opp.
    simpl.
    destruct x.
    simpl.
    destruct x.
    destruct p.
    destruct (dec (Feq f 0)); intuition idtac.
    reflexivity.
    repeat rewrite field_div_definition.
    rewrite (@opp_mul_eq (f1 * Finv (f ^ 3))).
    rewrite (opp_mul_eq).
    symmetry.
    apply associative.
  Qed.

  Theorem jac_opp_correct : forall (a : point),
    Jacobian.eq (add a (opp a)) zero_point.

    intros.
    apply jac_eq_from_affine.
    rewrite to_affine_add.
    rewrite to_affine_zero.
    rewrite to_affine_opp.
    apply right_inverse.
  Qed.

  Theorem w_add_same_r : forall (z x y : wpoint),
    WeierstrassCurve.W.eq x y ->
    WeierstrassCurve.W.eq (WeierstrassCurve.W.add x z) (WeierstrassCurve.W.add y z).

    intros.
    rewrite H.
    reflexivity.

  Qed.

  Theorem w_add_same_r_if : forall (z x y : wpoint),
    WeierstrassCurve.W.eq (WeierstrassCurve.W.add x z) (WeierstrassCurve.W.add y z) ->
    WeierstrassCurve.W.eq x y.

    intros.
    apply (@w_add_same_r (W_opp z)) in H.
    repeat rewrite <- associative in H.
    rewrite right_inverse in H.
    repeat rewrite right_identity in H.
    trivial.
  Qed.

  Theorem w_opp_add_distr : forall (x y : wpoint),
    WeierstrassCurve.W.eq (W_opp (WeierstrassCurve.W.add x y)) (WeierstrassCurve.W.add (W_opp x) (W_opp y)).

    intros.
    eapply (@w_add_same_r_if (WeierstrassCurve.W.add x y)).
    rewrite left_inverse.
    rewrite (commutative x).
    rewrite <- associative.
    rewrite (associative (W_opp y)).
    rewrite left_inverse.
    rewrite left_identity.
    rewrite left_inverse.
    reflexivity.
  Qed.


  Theorem jac_opp_add_distr : forall (a b : point),
   Jacobian.eq (opp (add a b)) (add (opp a) (opp b)).

    intros.
    apply jac_eq_from_affine.
    repeat rewrite to_affine_opp.
    repeat rewrite to_affine_add.
    repeat rewrite to_affine_opp.
    apply w_opp_add_distr.

  Qed.

  Theorem w_opp_involutive  : forall (x : wpoint),
    WeierstrassCurve.W.eq (W_opp (W_opp x)) x.

    intros.
    apply (@w_add_same_r_if (W_opp x)).
    rewrite left_inverse.
    rewrite right_inverse.
    reflexivity.

  Qed.

  Theorem jac_opp_involutive  : forall (a : point),
    Jacobian.eq (opp (opp a)) a.

    intros.
    intros.
    apply jac_eq_from_affine.
    repeat rewrite to_affine_opp.
    apply w_opp_involutive.
  Qed.

  Theorem jac_eq_jacobian_eq:
    forall p1 p2 : Jacobian.point,
    jac_eq (fromPoint p1) (fromPoint p2) -> Jacobian.eq p1 p2.

    intros.
    eauto.

  Qed.

  Theorem fromPoint_is_jacobian : forall p,
    is_jacobian (fromPoint p).

    intros.
    unfold is_jacobian, fromPoint.
    destruct p.
    simpl.
    trivial.
  Qed.

  Theorem jac_eq_is_jacobian : forall p1 p2,
    is_jacobian p1 ->
    jac_eq p1 p2 ->
    is_jacobian p2.

    intros.
    unfold is_jacobian, jac_eq in *.
    destruct p1. destruct p.
    destruct p2. destruct p.
    destruct (dec (Feq f2 0)).
    trivial.

    destruct (dec (Feq f 0)).
    intuition idtac.
    intuition idtac.

    apply (fmul_same_r (Finv (f2^2))) in H0.
    rewrite <- associative in H0.
    rewrite (commutative (f2^2) (Finv (f2^2))) in H0.
    rewrite left_multiplicative_inverse in H0.
    rewrite right_identity in H0.

    apply (fmul_same_r (Finv (f2^3))) in H3.
    rewrite <- associative in H3.
    rewrite (commutative (f2^3) (Finv (f2^3))) in H3.
    rewrite left_multiplicative_inverse in H3.
    rewrite right_identity in H3.

    rewrite H0 in H.
    rewrite H3 in H.
    repeat rewrite cube_mul_eq in H.
    repeat rewrite square_mul_eq in H.

    apply (fmul_same_r (Finv ((f^2)^3))) in H.
    rewrite (commutative (f4^2) ((f^2)^3)) in H.
    rewrite (commutative _ (Finv _)) in H.
    do 2 rewrite (associative (Finv ((f ^ 2) ^ 3))) in H.
    rewrite left_multiplicative_inverse in H.
    rewrite left_identity in H.
    repeat rewrite right_distributive in H.
    rewrite (commutative _ (Finv ((f^2)^3))) in H.
    rewrite (commutative (f3^3)) in H.
    do 2 rewrite (associative (Finv ((f ^ 2) ^ 3))) in H.
    rewrite left_multiplicative_inverse in H.
    rewrite left_identity in H.
    rewrite <- (associative b) in H.
    rewrite (commutative ((f^2)^3)) in H.
    rewrite left_multiplicative_inverse in H.
    rewrite right_identity in H.
    setoid_replace (a * (f3 * f ^ 2 * Finv (f2 ^ 2)) * (f ^ 2) ^ 2 * Finv ((f ^ 2) ^ 3))
        with (a * (f3 * Finv (f2 ^ 2)))
        in H.
    apply (fmul_same_r ((f2^3)^2)) in H.
    rewrite <- (associative) in H.
    rewrite inv_square_eq in H.
    rewrite left_multiplicative_inverse in H.
    rewrite right_identity in H.
    rewrite H.
    repeat rewrite right_distributive.
    rewrite <- (associative (f3^3)).
    repeat rewrite inv_cube_eq.
    repeat rewrite cube_square_eq.
    rewrite left_multiplicative_inverse.
    rewrite right_identity.
    apply fadd_same_r.
    repeat rewrite (commutative (f3^3)).
    apply fadd_same_r.
    repeat rewrite <- (associative a).
    repeat rewrite (commutative a).
    apply fmul_same_r.
    rewrite <- (associative f3).
    repeat rewrite (commutative f3).
    apply fmul_same_r.
    setoid_replace ((f2^2)^3) with ((f2^2) * ((f2^2)^2)).
    rewrite (associative (Finv (f2^2))).
    rewrite left_multiplicative_inverse.
    rewrite left_identity.
    reflexivity.
    apply square_nz; trivial.
    repeat rewrite associative.
    reflexivity.
    eauto using square_nz, cube_nz.
    eauto using square_nz, cube_nz.
    eauto using square_nz, cube_nz.
    eauto using square_nz, cube_nz.

    repeat rewrite <- (associative a).
    repeat rewrite (commutative a).
    apply fmul_same_r.
    repeat rewrite <- (associative f3).
    repeat rewrite (commutative f3).
    apply fmul_same_r.
    rewrite (commutative (f^2)).
    repeat rewrite <- (associative (Finv (f2^2))).
    setoid_replace (f ^ 2 * (f ^ 2) ^ 2) with ((f ^ 2) ^ 3).
    rewrite (commutative ((f^2)^3)).
    rewrite left_multiplicative_inverse.
    rewrite right_identity.
    reflexivity.
    eauto using square_nz, cube_nz.
    repeat rewrite associative.
    reflexivity.

    eauto using square_nz, cube_nz.
    eauto using square_nz, cube_nz.
    eauto using square_nz, cube_nz.
    eauto using square_nz, cube_nz.
    eauto using square_nz, cube_nz.

  Qed.

  Theorem fromPoint_toPoint_id : forall p (H : is_jacobian p),
    p = fromPoint (toPoint _ H).
  
    intros.
    reflexivity.
  Qed.

  Theorem jac_eq_point_ex : forall p1 p2,
    jac_eq (fromPoint p1) p2 ->
    exists p2', p2 = fromPoint p2'.

    intros.
    assert (is_jacobian p2).
    eapply jac_eq_is_jacobian; eauto.
    apply fromPoint_is_jacobian.
    exists (toPoint _ H0).
    reflexivity.
  Qed.

  Theorem Proper_double_minus_3: forall (x y : point),
    Jacobian.eq x y -> 
    Jacobian.eq (Jacobian.double_minus_3 a_is_minus_3 x) (Jacobian.double_minus_3 a_is_minus_3 y).

    intros.
    repeat rewrite <- Jacobian.double_minus_3_eq_double.
    apply Jacobian.Proper_double.
    trivial.

  Qed.


End CurveFacts.

Global Instance EC_CommutativeGroup : forall `{Curve}{Feq_dec : DecidableRel Feq}, 
  (CommutativeGroup point jac_eq_setoid).

  econstructor; intros.
  apply Jacobian.Proper_add.
  eapply jac_add_assoc.
  eapply jac_add_comm.
  apply jac_add_id_l.
  apply Proper_opp.
  apply jac_opp_correct.
Defined.

Global Instance EC_CommutativeGroupWithDouble : forall `{Curve}{Feq_dec : DecidableRel Feq},
  (CommutativeGroupWithDouble EC_CommutativeGroup).

  econstructor.
  apply Jacobian.Proper_double. 
  intros.
  apply jac_double_correct.

Defined.

(* Some facts follow from Fermat's little theorem for finite fields. Rather than giving a 
complete definition, we will simply define a structure on which the theorem is assumed to hold. 
The field_order value is a predicate to avoid performance issues when exact numeric values are used. *)
Class FiniteField{field_order : nat -> Prop}(F : Type)(Feq : F -> F -> Prop)`{field F Feq} :=
{
  fermat_little_theorem : forall x, field_order x -> forall y, Feq (Fpow x y) y
}.


