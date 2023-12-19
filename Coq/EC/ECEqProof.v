(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0 *)

(* Proof of equivalence and correctness for extracted scalar/point multiplication operation. *)

From Coq Require Import Lists.List.
From Coq Require Import String.
From Coq Require Import Vectors.Vector.
From Coq Require Import BinPos.
From Coq Require Import Ring.
From Coq Require Import Setoid.
From Coq Require Import ZArith.BinInt.
From Coq Require Import Classes.SetoidClass.
From Coq Require Import Lia.

From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
Import ListNotations.

From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.
From CryptolToCoq Require Import SAWCorePrelude.
Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCorePreludeExtra.

From CryptolToCoq Require Import SAWCoreBitvectors.

From Bits Require Import operations.
From Bits Require Import operations.properties.

From Crypto Require Import Algebra.Hierarchy.
From Crypto Require Import Algebra.Field.
From Crypto Require Import Algebra.Nsatz.

From Crypto Require Import Curves.Weierstrass.Jacobian.
From Crypto Require Import Curves.Weierstrass.Affine.
From Crypto Require Import Curves.Weierstrass.AffineProofs.


From EC Require Import GroupMulWNAF.
From EC Require Import EC_P384_5.
From EC Require Import EC_P384_Abstract.
From EC Require Import CryptolToCoq_equiv.
From EC Require Import WindowedMulMachine.
From EC Require Import GeneratorMul.

Set Implicit Arguments.

Require Import CryptolToCoq.SAWCoreVectorsAsCoqVectors.


Section ECEqProof.

  Definition F := seq 6 (seq 64 Bool).

  Definition Fzero : F := (replicate 6 _ (replicate 64 _ false)).
  Variable Fone : F.
  Variable Fopp  : F -> F.
  Variable Fadd  : F -> F -> F.
  Variable Fsub  : F -> F -> F.
  Variable Fmul  : F -> F -> F.
  Variable Finv : F -> F.
  Definition Fdiv (x y:F) := Fmul x (Finv y).

  Local Notation "0" := Fzero.  Local Notation "1" := Fone.
  Local Infix "+" := Fadd. Local Infix "-" := Fsub.
  Local Infix "*" := Fmul. Local Infix "/" := Fdiv.
  Local Notation "x ^ 2" := (x*x) (at level 30).
  Local Notation "x ^ 3" := (x^2*x) (at level 30).

  Theorem felem_nz_eq_0 : 
    (felem_nz 0) = (intToBv 64 0).

    reflexivity.

  Qed.

  Theorem felem_nz_neq_0 : forall x,
    x <> 0 ->
    (felem_nz x) <> (intToBv 64 0).

    intuition.
    eapply H.
    eapply fold_or_impl_0; eauto.

  Qed.

  (* Here, we assume that the basic operations form a field up to strict equality.
   *)
  Definition Feq := (@eq F).
  Hypothesis F_Field : @field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv.
  Existing Instance F_Field.

  (* Now we prove that equality is decidable.*)
  Theorem Vector_eq_dec : forall (A : Type)(n : nat)(v1 v2 : VectorDef.t A n),
    (forall (a1 a2 : A), {a1 = a2} + {a1 <> a2}) ->
    {v1 = v2} + {v1 <> v2}.

    induction n; intros; simpl in *.
    left.
    apply vec_0_eq.
    rewrite (eta v1).
    rewrite (eta v2).
    destruct (X (hd v1) (hd v2)).
    destruct (IHn (tl v1) (tl v2)); eauto.
    left.
    f_equal; eauto.
    right.
    intuition idtac.
    apply cons_inj in H.
    intuition idtac.
    right.
    intuition idtac.
    apply cons_inj in H.
    intuition idtac.

  Qed.

  Theorem Feq_dec : DecidableRel Feq.

    unfold Decidable.
    intros.
    apply Vector_eq_dec.
    intros.
    apply Vector_eq_dec.
    intros.
    decide equality.
  Qed.
  Existing Instance Feq_dec.

  (* Assume the field has characteristic at least 28. This enables a simple proof that the discriminant is nonzero. *)
  Hypothesis Fchar_28 : @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 28.
  Existing Instance Fchar_28.

  (* The field must have characteristic at least 12 in order for the base point to generate a group. *)
  Theorem Fchar_12 : @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 12.
    eapply char_ge_weaken.
    eauto.
    lia.

  Qed.
  Existing Instance Fchar_12.

  (* Point addition requires the field to have characteristic at least 3. *)
  Theorem Fchar_3 : @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 3.

    eapply char_ge_weaken.
    eauto.
    lia.

  Qed.
  Existing Instance Fchar_3.

  (* Here, we posit abstract EC curve parameters.  We could probably
     take the actual values for P-384 instead.
   *)
  Variable a : F.
  Variable b : F.

  (* Now we can instantiate the type of points on the
     curve in Jacobian/projective coordinates.
   *)
  Definition point := @Jacobian.point F Feq Fzero Fadd Fmul a b Feq_dec.


  Definition fromPoint (p:point) : (F*F*F) :=
    proj1_sig p.

  Definition prodToSeq(p : F * F * F) : seq 3 F :=
    cons _ (fst (fst p)) _ (cons _ (snd (fst p)) _ (cons _ (snd p) _ (@nil F))).

  Theorem zero_lt_three : 0 < 3.
    intuition eauto.
  Qed.

  Theorem one_lt_three : 1 < 3.
    intuition eauto.
  Qed.

  Theorem two_lt_three : 2 < 3.
    intuition eauto.
  Qed.

  Definition seqToProd(p : seq 3 F) : F * F * F :=
    (nth_order p zero_lt_three, nth_order p one_lt_three, nth_order p two_lt_three).

  Definition is_jacobian (p : F * F * F) :=
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

  Definition zero_point_h : F * F * F := (0, 1, 0).
  Theorem zero_point_is_jacobian : is_jacobian zero_point_h.

    unfold is_jacobian, zero_point_h.
    simpl.
    unfold Feq.
    destruct (dec (0 = 0)); intuition.

  Qed.

  Definition zero_point : point :=
    exist _ zero_point_h zero_point_is_jacobian.

  Definition toPoint(p : F * F * F)(pf : is_jacobian p) : point :=
    exist _ p pf.

  
  Definition jac_eq (p1 p2 : F * F * F) :=
    let '(X1, Y1, Z1) := p1 in
    let '(X2, Y2, Z2) := p2 in
      if dec (Feq Z1 Fzero)
      then Feq Z2 Fzero
      else
       ~ Feq Z2 Fzero /\
       Feq (Fmul X1 (Fmul Z2 Z2)) (Fmul X2 (Fmul Z1 Z1)) /\
       Feq (Fmul Y1 (Fmul (Fmul Z2 Z2) Z2)) (Fmul Y2 (Fmul (Fmul Z1 Z1) Z1)).

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
    x <> 0 ->
    x ^ 2 <> 0.

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
    x <> 0 ->
    x ^ 3 <> 0.

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

    eapply (@fmul_same_r (Finv (f^2))) in H0.
    rewrite <- (associative f3) in H0.
    rewrite (commutative (f^2)) in H0.
    rewrite left_multiplicative_inverse in H0.
    rewrite right_identity in H0.
    rewrite <- H0 in H2.
    eapply (@fmul_same_r (Finv (f2^2))) in H2.
    rewrite <- (associative f6) in H2.
    rewrite (commutative (f2^2)) in H2.
    rewrite left_multiplicative_inverse in H2.
    rewrite right_identity in H2.
    rewrite (commutative _ (Finv (f2^2))) in H2.
    rewrite (commutative f0) in H2.
    do 3 rewrite (associative (Finv (f2^2))) in H2.    
    rewrite left_multiplicative_inverse in H2.
    rewrite left_identity in H2.
    eapply (@fmul_same_r (f^2)) in H2.
    rewrite (commutative _ (f^2)) in H2.
    rewrite (commutative f0) in H2.
    do 2 rewrite (associative (f^2)) in H2.
    rewrite (commutative (f^2)) in H2.
    rewrite left_multiplicative_inverse in H2.
    rewrite left_identity in H2.
    trivial.

    eauto using square_nz.
    eauto using square_nz.
    eauto using square_nz.
    eauto using square_nz.  
    
    eapply (@fmul_same_r (Finv (f^3))) in H4.
    rewrite <- (associative f4) in H4.
    rewrite (commutative (f^3)) in H4.
    rewrite left_multiplicative_inverse in H4.
    rewrite right_identity in H4.
    rewrite <- H4 in H5.
    eapply (@fmul_same_r (Finv (f2^3))) in H5.
    rewrite <- (associative f7) in H5.
    rewrite (commutative (f2^3)) in H5.
    rewrite left_multiplicative_inverse in H5.
    rewrite right_identity in H5.
    rewrite (commutative _ (Finv (f2^3))) in H5.
    rewrite (commutative f1) in H5.
    do 3 rewrite (associative (Finv (f2^3))) in H5.    
    rewrite left_multiplicative_inverse in H5.
    rewrite left_identity in H5.
    eapply (@fmul_same_r (f^3)) in H5.
    rewrite (commutative _ (f^3)) in H5.
    rewrite (commutative f1) in H5.
    do 2 rewrite (associative (f^3)) in H5.
    rewrite (commutative (f^3)) in H5.
    rewrite left_multiplicative_inverse in H5.
    rewrite left_identity in H5.
    trivial.
    
    eauto using cube_nz.
    eauto using cube_nz.
    eauto using cube_nz.
    eauto using cube_nz.

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

  Definition Fsquare x := Fmul x x.
  Local Opaque Fsquare.

  Definition point_add := point_add Fsquare Fmul Fsub Fadd.
  Definition point_add_jac := point_add false.

  Definition point_add_jac_prod (p1 p2 : (F * F * F)) : (F * F * F) :=
    let p3 := point_add_jac (prodToSeq p1) (prodToSeq p2) in
    (seqToProd p3).


  (* Prove that squaring satisifes its spec. *)
  Theorem felem_sqr_spec : forall (x : F), Fsquare x = Fmul x x.

    intros. reflexivity.
  Qed.

  (* Assume that the curve parameter a = -3, as it is for P-384 and other curves in the same family *)
  Hypothesis a_is_minus_3 : a = Fopp (1 + 1 + 1).

  (* Now, we can prove that the extracted Cryptol code computes the
     same point (up to strict equality) as the specialized (for a = -3)
     point-doubling procedure from fiat-crypto.
  *)
  Definition point_double := point_double Fsquare Fmul Fsub Fadd.

  Lemma double_eq_minus_3_h : forall p:point,
      fromPoint (Jacobian.double_minus_3 a_is_minus_3 p) =
      seqToProd (point_double (prodToSeq (fromPoint p))).
  Proof.

      intros [ [[x y] z] Hp ]; simpl.
      unfold prodToSeq, seqToProd, fromPoint, point_double, EC_P384_5.point_double; simpl.      
      unfold nth_order, nth. simpl.
      unfold sawAt, atWithDefault. simpl.
      repeat rewrite felem_sqr_spec.
    
      f_equal; intros.
      nsatz.
  
  Qed.

  Theorem prodToSeq_inv : forall x, prodToSeq (seqToProd x) = x.

    intros.
    unfold seqToProd, prodToSeq.
    simpl.
    destruct (Vec_S_cons _ _ x).
    destruct H.
    destruct (Vec_S_cons _ _ x1).
    destruct H0.
    destruct (Vec_S_cons _ _ x3).
    destruct H1.
    subst.
    rewrite (Vec_0_nil _ x5).
    reflexivity.
  Qed.

  Theorem seqToProd_inv : forall x, seqToProd (prodToSeq x) = x.
    intros.
    unfold seqToProd, prodToSeq.
    simpl.
    destruct x.
    destruct p.
    reflexivity.
  Qed.

  Theorem double_eq_minus_3 : forall p:point,
      prodToSeq (fromPoint (Jacobian.double_minus_3 a_is_minus_3 p)) =
      (point_double (prodToSeq (fromPoint p))).

    intros.
    rewrite double_eq_minus_3_h.
    rewrite prodToSeq_inv.
    reflexivity.

  Qed.

  Lemma point_add_jac_eq_h : forall (a b:point),
      jac_eq (fromPoint (Jacobian.add a b))
      (seqToProd (point_add_jac (prodToSeq (fromPoint a)) (prodToSeq (fromPoint b)))).
  Proof.
      intros [ [[xa ya] za] Ha ] [ [[xb yb] zb] Hb ]; simpl.
    
      unfold point_add_jac, fromPoint, point_add, EC_P384_Abstract.point_add, EC_P384_5.point_add, ecNotEq, ecEq, ecZero, ecAnd, ecOr, ecCompl, felem_cmovznz; simpl.
      repeat rewrite felem_sqr_spec.
      unfold sawAt, atWithDefault. simpl.
      
      replace ((negb (if dec (xb * za ^ 2 - xa * zb ^ 2 = Fzero) then 0 else 1) &&
     negb (if dec (yb * (za * za ^ 2) - zb * zb ^ 2 * ya + (yb * (za * za ^ 2) - zb * zb ^ 2 * ya) = Fzero) then 0 else 1) &&
     (if dec (za = Fzero) then 0 else 1) && (if dec (zb = Fzero) then 0 else 1))%bool) with 
      (testForDouble za zb (xb * za ^ 2 - xa * zb ^ 2)
    (yb * (za * za ^ 2) - zb * zb ^ 2 * ya + (yb * (za * za ^ 2) - zb * zb ^ 2 * ya))).

      case_eq (testForDouble za zb (xb * za ^ 2 - xa * zb ^ 2)
      (yb * (za * za ^ 2) - zb * zb ^ 2 * ya +
       (yb * (za * za ^ 2) - zb * zb ^ 2 * ya))); intros.

      replace (xa, ya, za) with (fromPoint
       (exist (fun '(X, Y, Z) => if dec (Z = 0) then True else Y ^ 2 = X ^ 3 + a * X * (Z ^ 2) ^ 2 + b * (Z ^ 3) ^ 2)
          (xa, ya, za) Ha)).
      rewrite <- double_eq_minus_3.
      rewrite seqToProd_inv.

      eapply jac_eq_trans; [idtac | apply jacobian_eq_jac_eq; apply Jacobian.double_minus_3_eq_double].
      apply jac_eq_refl_abstract.
   
      unfold Jacobian.double, fromPoint; simpl.
      reflexivity.
      trivial.

      apply jac_eq_refl_abstract.
      unfold Feq, seqToProd, nth_order, nth. simpl.
      destruct (dec (zb = 0)); subst.
      rewrite felem_nz_eq_0.
      rewrite ecEq_bv_true.
      trivial.
      destruct (dec (za = 0)); subst.
      rewrite felem_nz_eq_0.
      rewrite ecEq_bv_true.
      rewrite ecEq_bv_false.
      trivial.
      eapply felem_nz_neq_0.
      trivial.
      repeat rewrite ecEq_bv_false; simpl.
      reflexivity.
      eapply felem_nz_neq_0. trivial.
      eapply felem_nz_neq_0. trivial.

      unfold testForDouble.
      destruct (dec (xb * za ^ 2 - xa * zb ^ 2 = 0)).
      simpl.
      rewrite e.
      rewrite <- rep_false_eq_int_bv.
      
      rewrite ecEq_vec_bv_true.
      unfold ecAnd. simpl.
      destruct (dec (yb * (za * za ^ 2) - zb * zb ^ 2 * ya + (yb * (za * za ^ 2) - zb * zb ^ 2 * ya) = 0)).
      rewrite e0.
      rewrite ecEq_vec_bv_true.
      simpl.
      destruct (dec (za = 0)).
      rewrite e1.
      rewrite ecNotEq_vec_bv_false.
      trivial.
      rewrite ecNotEq_vec_bv_true; intuition.
      simpl.
      destruct (dec (zb = 0)).
      rewrite e1.
      rewrite ecNotEq_vec_bv_false.
      trivial.
      rewrite ecNotEq_vec_bv_true; intuition.
      rewrite ecEq_vec_bv_false; intuition.

      simpl.
      rewrite ecEq_vec_bv_false; intuition.

  Qed.

  Definition point_add_mixed := point_add true.

  Definition isAffine (p : point) :=
    (snd (proj1_sig p) = Fone).

  Lemma point_add_mixed_eq_h : forall (a b:point),
      isAffine b -> 
      jac_eq (fromPoint (Jacobian.add a b))
      (seqToProd (point_add_mixed (prodToSeq (fromPoint a)) (prodToSeq (fromPoint b)))).

    intros [ [[xa ya] za] Ha ] [ [[xb yb] zb] Hb ]; intros; simpl.
    unfold point_add_mixed, fromPoint, point_add, EC_P384_Abstract.point_add, EC_P384_5.point_add, ecNotEq, ecEq, ecZero, ecAnd, ecOr, ecCompl, felem_cmovznz; simpl.
      repeat rewrite felem_sqr_spec.
      unfold sawAt, atWithDefault. simpl.
    
      replace ((negb (if dec (xb * za ^ 2 - xa * zb ^ 2 = Fzero) then 0 else 1) &&
     negb (if dec (yb * (za * za ^ 2) - zb * zb ^ 2 * ya + (yb * (za * za ^ 2) - zb * zb ^ 2 * ya) = Fzero) then 0 else 1) &&
     (if dec (za = Fzero) then 0 else 1) && (if dec (zb = Fzero) then 0 else 1))%bool) with 
      (testForDouble za zb (xb * za ^ 2 - xa * zb ^ 2)
    (yb * (za * za ^ 2) - zb * zb ^ 2 * ya + (yb * (za * za ^ 2) - zb * zb ^ 2 * ya))).
      unfold isAffine in *.
      simpl in *.
      subst zb.
      replace (xb * za ^ 2 - xa * 1 ^ 2) with (xb * za ^ 2 - xa); try nsatz.
      replace (yb * (za * za ^ 2) - 1 * 1 ^ 2 * ya + (yb * (za * za ^ 2) - 1 * 1 ^ 2 * ya)) with
        (yb * (za * za ^ 2) - ya + (yb * (za * za ^ 2) - ya)); try nsatz.
      case_eq (testForDouble za 1 (xb * za ^ 2 - xa) (yb * (za * za ^ 2) - ya + (yb * (za * za ^ 2) - ya))); intros.

      replace (xa, ya, za) with (fromPoint
       (exist (fun '(X, Y, Z) => if dec (Z = 0) then True else Y ^ 2 = X ^ 3 + a * X * (Z ^ 2) ^ 2 + b * (Z ^ 3) ^ 2)
          (xa, ya, za) Ha)).
      rewrite <- double_eq_minus_3.
      rewrite seqToProd_inv.

      eapply jac_eq_trans; [idtac | apply jacobian_eq_jac_eq; apply Jacobian.double_minus_3_eq_double].
      apply jac_eq_refl_abstract.
   
      unfold Jacobian.double, fromPoint; simpl.
      reflexivity.
      trivial.

      apply jac_eq_refl_abstract.
      unfold Feq, seqToProd, nth_order, nth. simpl.
      destruct (dec (1 = 0)); subst.
      rewrite ecEq_bv_true.
      reflexivity.
      rewrite ecEq_bv_false.

      destruct (dec (za = 0) ).
      subst za.
      rewrite ecEq_bv_true.
      trivial.

      rewrite ecEq_bv_false.
      f_equal.
      f_equal.
      nsatz.
      nsatz.
      nsatz.
      eapply felem_nz_neq_0. trivial.
      eapply felem_nz_neq_0. trivial.

      unfold testForDouble.
      destruct (dec (xb * za ^ 2 - xa * zb ^ 2 = 0)).
      simpl.
      rewrite e.
      rewrite <- rep_false_eq_int_bv.
      
      rewrite ecEq_vec_bv_true.
      unfold ecAnd. simpl.
      destruct (dec (yb * (za * za ^ 2) - zb * zb ^ 2 * ya + (yb * (za * za ^ 2) - zb * zb ^ 2 * ya) = 0)).
      rewrite e0.
      rewrite ecEq_vec_bv_true.
      simpl.
      destruct (dec (za = 0)).
      rewrite e1.
      rewrite ecNotEq_vec_bv_false.
      trivial.
      rewrite ecNotEq_vec_bv_true; intuition.
      simpl.
      destruct (dec (zb = 0)).
      rewrite e1.
      rewrite ecNotEq_vec_bv_false.
      trivial.
      rewrite ecNotEq_vec_bv_true; intuition.
      rewrite ecEq_vec_bv_false; intuition.

      simpl.
      rewrite ecEq_vec_bv_false; intuition.
    Qed.


  Theorem square_mul_eq : forall (x y : F),
    (x * y)^2 = x^2 * y^2.
  
    intros.
    repeat rewrite associative.
    f_equal.
    rewrite <- (associative x x).  
    rewrite <- associative.
    f_equal.
    apply commutative.
  Qed.

  Theorem cube_mul_eq : forall (x y : F),
    (x * y)^3 = x^3 * y^3.

    intros.
    rewrite square_mul_eq.
    repeat rewrite <- (associative (x^2)).
    f_equal.
    rewrite (commutative x (y^3)).
    rewrite <- (associative (y^2)).
    f_equal.
    apply commutative.
  Qed.


  Theorem jac_eq_jacobian_eq:
    forall p1 p2 : Jacobian.point,
    jac_eq (fromPoint p1) (fromPoint p2) -> Jacobian.eq p1 p2.

    intros.
    eauto.

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

  Theorem inv_mul_eq : forall (x y : F),
    ~(Feq y 0) ->
    ~(Feq x 0) ->
    Finv (x*y) = ((Finv x) * (Finv y)).

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
    (Finv x)^2 = Finv (x^2).

    symmetry.
    apply inv_mul_eq; eauto.

  Qed.

  Theorem inv_cube_eq : forall (x : F),
    ~(Feq x 0) ->
    (Finv x)^3 = Finv (x^3).

    symmetry.
    rewrite inv_mul_eq; eauto.
    rewrite inv_square_eq; eauto.
    apply square_nz; trivial.

  Qed.

  Theorem fromPoint_is_jacobian : forall p,
    is_jacobian (fromPoint p).

    intros.
    unfold is_jacobian, fromPoint.
    destruct p.
    simpl.
    trivial.
  Qed.

  Theorem cube_square_eq : forall (x : F),
    ((x^3)^2) = ((x^2)^3).

    intros.
    repeat rewrite associative.
    reflexivity.

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
    repeat rewrite cube_mul_eq in *.
    repeat rewrite square_mul_eq in *.

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
    replace (a * (f3 * f ^ 2 * Finv (f2 ^ 2)) * (f ^ 2) ^ 2 * Finv ((f ^ 2) ^ 3))
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
    replace ((f2^2)^3) with ((f2^2) * ((f2^2)^2)).
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
    replace (f ^ 2 * (f ^ 2) ^ 2) with ((f ^ 2) ^ 3).
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

 
  (* A more general form of the point add correctness proof using Jacobian equality *)
  Lemma point_add_jac_eq : forall (a b:point) a' b',
    jac_eq (fromPoint a) (seqToProd a') ->
    jac_eq (fromPoint b) (seqToProd b') -> 
    jac_eq (fromPoint (Jacobian.add a b)) (seqToProd (point_add_jac a' b')).

    intros.  
    edestruct (jac_eq_point_ex _ _ H).
    edestruct (jac_eq_point_ex _ _ H0).
    
    eapply jac_eq_trans.
    eapply jacobian_eq_jac_eq.
    eapply Jacobian.Proper_add.
    eapply jac_eq_jacobian_eq.
    rewrite H1 in H.
    eauto.
    eapply jac_eq_jacobian_eq.
    rewrite H2 in H0.
    eauto.
    eapply jac_eq_trans.
    eapply point_add_jac_eq_h.
    rewrite <- H1.
    rewrite <- H2.
    repeat rewrite prodToSeq_inv.
    apply jac_eq_refl.
 
  Qed.

  Lemma point_add_mixed_eq : forall (a b:point) a' b',
    nth_order b' two_lt_three = Fone -> 
    jac_eq (fromPoint a) (seqToProd a') ->
    jac_eq (fromPoint b) (seqToProd b') -> 
    jac_eq (fromPoint (Jacobian.add a b)) (seqToProd (point_add_mixed a' b')).

    intros.  
    edestruct (jac_eq_point_ex _ _ H0).
    edestruct (jac_eq_point_ex _ _ H1).
    
    eapply jac_eq_trans.
    eapply jacobian_eq_jac_eq.
    eapply Jacobian.Proper_add.
    eapply jac_eq_jacobian_eq.
    rewrite H2 in H0.
    eauto.
    eapply jac_eq_jacobian_eq.
    rewrite H3 in H1.
    eauto.
    eapply jac_eq_trans.
    eapply point_add_mixed_eq_h.
    unfold isAffine in *.
    destruct x0.
    simpl in *.
    subst.
    destruct (Vec_S_cons _ _ b'). destruct H.
    destruct (Vec_S_cons _ _ x1). destruct H3.
    destruct (Vec_S_cons _ _ x3). destruct H4.
    subst.
    rewrite (Vec_0_nil _ x5).
    simpl.
    reflexivity.
    
    rewrite <- H2.
    rewrite <- H3.
    repeat rewrite prodToSeq_inv.
    apply jac_eq_refl.
 
  Qed.


  Definition point_mul := point_mul Fsquare Fmul Fsub Fadd Fopp.

  (* Jacobian.v defines an Equivalence instance for Jacobian.eq. Use this to construct a Setoid. *)
  Instance jac_eq_setoid : Setoid point := {equiv := Jacobian.eq}.

  Theorem jac_eq_from_affine : forall (x y : point),
    WeierstrassCurve.W.eq (Jacobian.to_affine x) (Jacobian.to_affine y) ->
    x == y.
  
    intros.
    rewrite <- Jacobian.of_affine_to_affine.
    symmetry.
    rewrite <- Jacobian.of_affine_to_affine.
    symmetry.
    apply Jacobian.Proper_of_affine.
    trivial.
  Qed.

  Definition wpoint := @WeierstrassCurve.W.point F Feq Fadd Fmul a b.

  Definition W_opp : wpoint -> wpoint := W.opp.

  
  (* Discriminant is non-zero *)
  (* When a=-3 and characerteristic is large, this follows from b<>2 and b<>-2 *)
  Variable b_ne_plus_minus_2 : 
    ~((Feq b (1 + 1)) \/ (Feq b (Fopp (1 + 1)))).

  Theorem discriminant_nonzero :
    ~
  Feq
  ((1 + 1 + 1 + 1) * a * a * a +
   ((1 + 1 + 1 + 1) ^ 2 + (1 + 1 + 1 + 1) + (1 + 1 + 1 + 1) + 1 + 1 + 1) * b * b) 0.

    intros.
    repeat rewrite a_is_minus_3.
    replace ((1 + 1 + 1 + 1) * Fopp (1 + 1 + 1) * Fopp (1 + 1 + 1) * Fopp (1 + 1 + 1)) with (((1 + 1 + 1)^3) * (Fopp (1 + 1 + 1 + 1))).
    replace (((1 + 1 + 1 + 1) ^ 2 + (1 + 1 + 1 + 1) + (1 + 1 + 1 + 1) + 1 + 1 + 1) * b * b) with (((1 + 1 + 1)^3) * (b^2)).
    unfold Logic.not.
    intros.

    assert (~ Feq (1 + (1 + 1) * (1 + (1 + 1) * ((1 + 1) * (1 + (1 + 1))))) 0).
    unfold Ring.char_ge in *.
    unfold char_ge in *.
    replace (1 + (1 + 1) * (1 + (1 + 1) * ((1 + 1) * (1 + (1 + 1))))) with (@Ring.of_Z felem 0 1 Fopp Fadd  (Z.pos 27)).
    eapply Fchar_28.
    lia.
    simpl.
    nsatz.
    assert (Feq (b^2) ((1 + 1)^2)).
    nsatz.

    assert (Feq ((b + (1 + 1)) * (b  + (Fopp (1 + 1)))) 0).
    nsatz.
    destruct (Feq_dec b (1+1)).
    apply b_ne_plus_minus_2.
    left.
    trivial.
    apply b_ne_plus_minus_2.
    right.
    assert (Feq ((b + (1 + 1)) * ((Finv (b + Fopp (1 + 1)))* ( (b + Fopp (1 + 1))))) 0).
    nsatz.
    rewrite left_multiplicative_inverse in H3.
    nsatz.
    intuition idtac.
    eapply H5.
    nsatz.

    nsatz.
    nsatz.

  Qed.

  Instance W_commutative_group : 
    @commutative_group wpoint
    WeierstrassCurve.W.eq
    WeierstrassCurve.W.add
    WeierstrassCurve.W.zero
    W.opp.

    apply W.commutative_group.
    apply Fchar_12.
    unfold Datatypes.id.
    apply discriminant_nonzero.  

  Defined.


  Theorem jac_add_assoc : forall (x y z : point),
    (Jacobian.add (Jacobian.add x y) z) == (Jacobian.add x (Jacobian.add y z)).

    intros.
    apply jac_eq_from_affine.

    repeat rewrite Jacobian.to_affine_add.
    rewrite associative.
    reflexivity.

  Qed.

  Theorem jac_add_comm : forall (a b : point),
    (Jacobian.add a b) == (Jacobian.add b a).

    intros.
    apply jac_eq_from_affine.
    repeat rewrite Jacobian.to_affine_add.
    apply commutative.

  Qed.

  Theorem to_affine_zero : WeierstrassCurve.W.eq (Jacobian.to_affine zero_point) WeierstrassCurve.W.zero.

    unfold WeierstrassCurve.W.eq, Jacobian.to_affine, zero_point.
    simpl.
    destruct (dec (Feq 0 0)); trivial.
    intuition idtac.
    eapply n.
    reflexivity.
  Qed.

  Theorem jac_add_id_l : forall (a : point),
    (Jacobian.add zero_point a) == a.

    intros.
    apply jac_eq_from_affine.
    repeat rewrite Jacobian.to_affine_add.
    rewrite to_affine_zero.  
    apply left_identity.

  Qed.

  Theorem jac_double_correct : forall (a : point),
    (Jacobian.double a) == (Jacobian.add a a).

    intros.
    apply jac_eq_from_affine.
    rewrite Jacobian.to_affine_add.
    rewrite Jacobian.to_affine_double.
    reflexivity.

  Qed.

  Theorem opp_mul_eq : forall (x : F),
    Feq (Fopp x) ((Fopp 1) * x).

    intros.
    eapply (@fadd_same_r_if x).
    rewrite left_inverse.
    replace x with (1 * x) at 2.
    rewrite <- right_distributive.
    rewrite left_inverse.
    symmetry.
    rewrite commutative.
    apply f_zero_absorb.
    apply left_identity.

  Qed.

  Theorem fmul_same_l:
    forall [x y z : F],
    Feq y z ->
    Feq (x * y) (x * z).

    intros.
    rewrite H.
    reflexivity.
  Qed.

  Theorem Proper_opp : Proper (Jacobian.eq ==> Jacobian.eq) (@Jacobian.opp F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b F_Field Feq_dec).
  
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
    WeierstrassCurve.W.eq (Jacobian.to_affine (Jacobian.opp x)) (W_opp (Jacobian.to_affine x)).

    intros.

    unfold WeierstrassCurve.W.eq, Jacobian.to_affine, Jacobian.opp, W_opp.
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
    (Jacobian.add a (Jacobian.opp a)) == zero_point.

    intros.
    apply jac_eq_from_affine.
    rewrite Jacobian.to_affine_add.
    rewrite to_affine_zero.
    rewrite to_affine_opp.
    apply right_inverse.
  Qed.

  Instance EC_CommutativeGroup : (CommutativeGroup point jac_eq_setoid).

    econstructor; intros.
    apply Jacobian.Proper_add.
    eapply jac_add_assoc.
    eapply jac_add_comm.
    apply jac_add_id_l.
    apply Proper_opp.
    apply jac_opp_correct.
  Defined.

  Instance EC_CommutativeGroupWithDouble : (CommutativeGroupWithDouble EC_CommutativeGroup).

    econstructor.
    apply Jacobian.Proper_double. 
    intros.
    apply jac_double_correct.

  Defined.

  Theorem preCompTable_h_cons : forall tsize p ls p2, 
    ls <> List.nil -> 
    (preCompTable_h tsize (p :: ls) p2) = 
    p :: (preCompTable_h tsize ls p2).

      induction tsize; unfold preCompTable_h in *; intuition; simpl in *.
      rewrite <- IHtsize.
      destruct ls; simpl in *. intuition.
      reflexivity.
      intuition.
      eapply app_cons_not_nil.
      symmetry.
      eauto.

  Qed.

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

 
  Definition wzero : wpoint := WeierstrassCurve.W.zero.

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
    (Jacobian.opp (Jacobian.add a b)) == (Jacobian.add (Jacobian.opp a) (Jacobian.opp b)).

    intros.
    apply jac_eq_from_affine.
    repeat rewrite to_affine_opp.
    repeat rewrite Jacobian.to_affine_add.
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
    (Jacobian.opp (Jacobian.opp a)) == a.

    intros.
    intros.
    apply jac_eq_from_affine.
    repeat rewrite to_affine_opp.
    apply w_opp_involutive.
  Qed.

  Definition seqToList(A : Type)(n : nat)(s : seq n A) : list A :=
    to_list s.

  Fixpoint preCompTable_fix (p : point) n prev :=
    match n with
    | O => prev :: List.nil
    | S n' => prev :: (preCompTable_fix p n'(Jacobian.add (Jacobian.double p) prev))
    end.

  Theorem seqTolist_cons : forall (A : Type)(n : nat) (x : A) (s : Vector.t A n),
    seqToList (cons _ x _ s) = List.cons x (seqToList s).

    intros.
    unfold seqToList, to_list. simpl.
    reflexivity.

  Qed.

  Local Opaque Jacobian.double Jacobian.add EC_P384_5.point_double EC_P384_5.point_add.

  Local Opaque sbvToInt.

  Theorem pow_add_lt : forall k x a b : Z,
    ((2^x) * a < 2^k ->
    b < x ->
    0 <= x ->
    k >= x ->
    (2^x)*a + 2^b < 2^k)%Z.  

    intros.
    remember (k - x)%Z as y.
    assert (a0 <= 2^y - 1)%Z.
    assert (a0 < 2^y)%Z.
    eapply (@Z.mul_lt_mono_pos_l (2^x)).
    eapply Z.pow_pos_nonneg; lia.
    eapply Z.lt_le_trans; eauto.
    subst.  
    rewrite <- Z.pow_add_r.
    rewrite Zplus_minus.
    reflexivity.
    lia.
    lia.
  
    lia.
    eapply Z.le_lt_trans.
    eapply (@Z.add_le_mono_r (2 ^ x * a0)).
    eapply Z.mul_le_mono_nonneg_l.
    eapply Z.pow_nonneg; lia.
    eauto.
    eapply Z.lt_le_trans.
    eapply (@Z.add_lt_mono_l (2 ^ b0)).
    eapply Z.pow_lt_mono_r; eauto.
    lia.
    eauto.
    rewrite Z.mul_sub_distr_l.
    rewrite Z.mul_1_r.
    rewrite Z.sub_simpl_r.
    subst.
    rewrite <- Z.pow_add_r.
    rewrite Zplus_minus.
    reflexivity.
    trivial.
    lia.

  Qed.


  Theorem sub_window_lt : forall n w k,
    (Z.of_nat (w + 1) <= k)%Z ->
    (0 <= n < 2^k)%Z ->
    ((n - (n mod 2 ^ Z.of_nat (w + 1) - 2^Z.of_nat w)) < 2^k)%Z.

    intros.
    rewrite Z.sub_sub_distr.
    assert (n = (2^Z.of_nat (w + 1) * (n / (2^Z.of_nat (w + 1) )) + n mod (2^Z.of_nat (w + 1) )))%Z.
    apply Z.div_mod.
    assert (0 < 2 ^ Z.of_nat (w + 1))%Z.
    eapply Z.pow_pos_nonneg; lia.
    lia.
    rewrite H1 at 1.
    rewrite <- Z.add_sub_assoc.
    rewrite Zminus_diag.
    rewrite Z.add_0_r.

    apply pow_add_lt.
    eapply Z.le_lt_trans; [idtac | apply H0].
    apply Z.mul_div_le.
    eapply Z.pow_pos_nonneg; lia.
    lia.
    lia.
    lia.

  Qed.

  Ltac bvIntSimpl_one :=
    match goal with
    | [|- ((bvToInt ?x _) < 2^(BinInt.Z.of_nat ?x))%Z] =>
      apply bvToInt_bound
    | [|- (0 <= bvToInt _ _)%Z] =>
      apply bvToInt_nonneg
    | [|- (- 2^_ <= 2^_)%Z] => eapply Z.le_trans; [apply Z.opp_nonpos_nonneg | idtac]
    | [|- context[sbvToInt _ (bvURem _ _ _ )]] => 
      rewrite sbvToInt_bvURem_equiv
    | [|- context[bvToInt _ (shiftL _ bool false (intToBv _ 1) _ ) ]] =>
      rewrite bvToInt_shiftL_1_equiv
    | [|- context[sbvToInt _ (shiftL _ bool false (intToBv _ 1) _ ) ]] =>
      rewrite sbvToInt_shiftL_1_equiv
    | [|- context[BinInt.Z.shiftl 1 _]] =>
      rewrite Z.shiftl_1_l
    | [|- (0 < _ ^ _)%Z] =>
      apply Z.pow_pos_nonneg
    | [|- (2^_ < 2^_)%Z] =>
      apply Z.pow_lt_mono_r
    | [|- (_ ^ _ <= _ ^ _)%Z] =>
      apply Z.pow_le_mono
    | [|- (_ <= _ mod _ < _)%Z] =>
      eapply bound_abstract; [apply Z.mod_pos_bound | idtac | idtac]
    | [|- Z.le (Z.opp _) _] =>
      apply Z.opp_nonpos_nonneg 
    | [|- (0 <= _ ^ _)%Z] =>
      apply Z.pow_nonneg
    | [|- (_ <= _ < _)%Z] =>
      split
    end.

  Ltac bvIntSimpl := repeat (bvIntSimpl_one; try lia).

  (* The spec of the scalar recoding function extracted from Cryptol uses scanl because that is what the Cryptol extraction supports.
  But a more natural way to write this spec in Coq is with a Fixpoint. Below, we write this function using a Fixpoint and prove it
  equal to the scanl form of the function. *)
  Fixpoint recode_rwnaf_odd_bv (wsize : nat)(nw : nat)(n : bitvector 384) :=
    match nw with
    | 0%nat => (drop _ 368 16 n) :: List.nil
    | S nw' =>
      let k_i := (bvSub _ (bvURem _ n (bvMul _ (bvNat _ 2) (shiftL _ _ false (bvNat _ 1%nat) wsize))) (shiftL _ _ false (bvNat _ 1%nat) wsize)) in
      let n' := (shiftR _ _ false (bvSub _ n k_i) wsize) in
      (drop _ 368 16 k_i) :: (recode_rwnaf_odd_bv wsize nw' n')
    end.

  Definition recode_rwnaf_odd_bv_scanl_fix_body wsize n :=
      let k_i := (bvSub _ (bvURem _ n (bvMul _ (bvNat _ 2) (shiftL _ _ false (bvNat _ 1%nat) wsize))) (shiftL _ _ false (bvNat _ 1%nat) wsize)) in
      let n' := (shiftR _ _ false (bvSub _ n k_i) wsize) in
      ((drop _ 368 16 k_i), n').

  Theorem recode_rwnaf_odd_bv_scanl_equiv : forall wsize nw n,
    nw > 0 ->
    recode_rwnaf_odd_bv wsize nw n = 
    scanl_fix 
      (fun p => recode_rwnaf_odd_bv_scanl_fix_body wsize (snd p))
      (fun p => fst p)
      (fun p => (drop _ 368 16 (snd p)))
      nw (recode_rwnaf_odd_bv_scanl_fix_body wsize n).

    induction nw; intros.
    lia.
    unfold recode_rwnaf_odd_bv.
    fold recode_rwnaf_odd_bv.
    unfold scanl_fix.
    fold scanl_fix.
    destruct nw.
    reflexivity.

    f_equal.
    eapply IHnw.
    lia.

  Qed.

  Theorem recode_rwnaf_odd_bv_equiv : 
    forall wsize nw n,
    0 < wsize < 16 -> 
    (bvToInt _ n < (Z.pow 2 (Z.of_nat ((S nw) * wsize))))%Z -> 
    List.Forall2 (fun (x : Z) (y : bitvector 16) => x = (sbvToInt _ y)) 
    (recode_rwnaf_odd wsize nw (bvToInt _ n)) 
    (recode_rwnaf_odd_bv wsize nw n).

    induction nw; intros.
    econstructor.
    rewrite sbvToInt_drop_equiv.
    rewrite bvToInt_sbvToInt_equiv.
    reflexivity.
    rewrite SAWCorePreludeExtra.addNat_add.
    lia.
    eapply Z.lt_le_trans; eauto.
    apply Z.pow_le_mono.
    lia.
    rewrite SAWCorePreludeExtra.addNat_add.
    lia.
    lia.
    rewrite bvToInt_sbvToInt_equiv.
    intuition idtac.
    eapply (Z.le_trans _ 0).
    apply Z.opp_nonpos_nonneg.
    eapply Z.pow_nonneg; lia.
    apply bvToInt_nonneg. 
    eapply Z.lt_le_trans.
    eapply H0.
    apply Z.pow_le_mono_r.
    lia.
    lia.
    rewrite addNat_add.
    lia.
    eapply Z.lt_le_trans.
    apply H0.
     rewrite addNat_add.
    apply Z.pow_le_mono; lia.
    econstructor.

    simpl.

    (* the calculated window value actually fits in a window*)
    assert ((- 2 ^ Z.of_nat wsize <=
     sbvToInt (addNat 368%nat 16%nat)
       (bvSub 384
          (bvURem 384 n
             (shiftL 384 bool false (intToBv 384%nat 1) (wsize + 1)))
          (shiftL 384 bool false (intToBv 384%nat 1) wsize)) <
     2 ^ Z.of_nat wsize)%Z).
    rewrite sbvToInt_bvSub_equiv.
    rewrite sbvToInt_bvURem_equiv.
    rewrite sbvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    apply Z_sub_range_le_lt_dbl_pos.
    apply Z.pow_nonneg; lia.
    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    rewrite Znat.Nat2Z.inj_add.
    rewrite Z.pow_add_r.
    rewrite Z.mul_comm.
    apply Z.mod_pos_bound.
    apply Z.mul_pos_pos; try lia.
    lia.
    lia.
    lia.
    lia.
    lia.
    lia.
    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    apply Z.pow_pos_nonneg; lia.
    lia.
    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    apply Z.pow_le_mono; lia.
    lia.
    lia.
    rewrite sbvToInt_bvURem_equiv.
    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    rewrite Znat.Nat2Z.inj_add.
    rewrite Z.pow_add_r.
    rewrite Z.mul_comm.
    eapply bound_abstract.
    apply Z.mod_pos_bound.
    apply Z.mul_pos_pos; try lia;
    apply Z.pow_pos_nonneg; lia.
    apply Z.opp_nonpos_nonneg.
    apply Z.pow_nonneg; lia.
    rewrite <- Z.pow_add_r.
    apply Z.pow_le_mono; lia.
    lia.
    lia.
    lia.
    lia.
    lia.
    lia.
    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    apply Z.pow_pos_nonneg; lia.
    lia.
    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    apply Z.pow_le_mono; lia.
    lia.
    rewrite sbvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    intuition idtac.
    eapply Z.le_trans.
    apply Z.opp_nonpos_nonneg.
    apply Z.pow_nonneg; lia.
    apply Z.pow_nonneg; lia.
    apply Z.pow_lt_mono_r; lia.
    lia.
    lia.

    match goal with
    | [|- List.Forall2 _ (?a :: _) (?b :: _)] =>
    assert (a = sbvToInt _ b)
    end.

    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    unfold twoToWsize.
    rewrite Zdouble_shiftl.
    rewrite sbvToInt_drop_equiv; try lia.
    rewrite sbvToInt_bvSub_equiv; try lia.
    f_equal.
    rewrite sbvToInt_bvURem_equiv; try lia.
    rewrite bvToInt_shiftL_1_equiv; try lia.
    f_equal. f_equal. lia.
    rewrite bvToInt_shiftL_1_equiv; try lia.
    rewrite Z.shiftl_1_l.
    apply Z.pow_pos_nonneg; lia.
    rewrite bvToInt_shiftL_1_equiv; try lia.
    rewrite Z.shiftl_1_l.
    apply Z.pow_le_mono_r; simpl; lia.

    rewrite sbvToInt_shiftL_1_equiv; simpl; lia.

    intros.
    split.
    eapply Z.le_trans.
    apply Z.opp_nonpos_nonneg.
    apply Z.pow_nonneg; lia.

    rewrite sbvToInt_bvURem_equiv; try lia.
    apply Z.mod_pos_bound.
    rewrite bvToInt_shiftL_1_equiv; try lia.
    rewrite Z.shiftl_1_l.
    apply Z.pow_pos_nonneg; lia.
    rewrite bvToInt_shiftL_1_equiv; try lia.
    rewrite Z.shiftl_1_l.
    apply Z.pow_pos_nonneg; lia.
    rewrite bvToInt_shiftL_1_equiv; try lia.
    rewrite Z.shiftl_1_l.
    eapply Z.pow_le_mono_r; simpl; lia.

    rewrite sbvToInt_bvURem_equiv; try lia.
    eapply Z.lt_le_trans.
    apply Z.mod_pos_bound.
    rewrite bvToInt_shiftL_1_equiv; try lia.
    rewrite Z.shiftl_1_l.
    apply Z.pow_pos_nonneg; lia.
    rewrite bvToInt_shiftL_1_equiv; try lia.
    rewrite Z.shiftl_1_l.
    apply Z.pow_le_mono_r; simpl; lia.
    rewrite bvToInt_shiftL_1_equiv; try lia.
    rewrite Z.shiftl_1_l.
    apply Z.pow_pos_nonneg; lia.

    rewrite bvToInt_shiftL_1_equiv; try lia.
    rewrite Z.shiftl_1_l.
    apply Z.pow_le_mono_r; simpl; lia.

    rewrite sbvToInt_shiftL_1_equiv; try lia.
    rewrite Z.shiftl_1_l.
    split.
    eapply Z.le_trans.
    apply Z.opp_nonpos_nonneg.
    apply Z.pow_nonneg; lia.
    apply Z.pow_nonneg; lia.
    apply Z.pow_lt_mono_r; simpl; lia.

    split.
    eapply Z.le_trans; [idtac | apply H1].
    apply (@Z.opp_le_mono (2 ^ Z.of_nat wsize)).
    apply Z.pow_le_mono_r; simpl; lia.
    eapply Z.lt_le_trans.
    apply H1.
    apply Z.pow_le_mono_r; simpl; lia.

    lia.
    lia.

    econstructor; eauto.

    match goal with
    | [|- List.Forall2 _ 
      (recode_rwnaf_odd _ _ ?a) (recode_rwnaf_odd_bv _ _ ?b)
    ] =>
    assert (a = (bvToInt _ b))
    end.

    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    rewrite bvToInt_shiftR_equiv.
    rewrite bvToInt_bvSub_small_equiv.
    rewrite sbvToInt_bvSub_equiv.
    rewrite sbvToInt_bvURem_equiv.
    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_mul_pow2.
    rewrite Z.mul_1_l.
    rewrite Z.shiftr_div_pow2.
 
    f_equal.
    f_equal.
    f_equal.
    unfold twoToWsize.
    rewrite Zdouble_shiftl.
    rewrite Z.shiftl_1_l.
    f_equal.
    f_equal.
    lia.
    lia.
    rewrite sbvToInt_shiftL_1_equiv.
    reflexivity.
    lia.
    lia.
    unfold twoToWsize.
    rewrite Z.shiftl_1_l.
    reflexivity.

    lia.
    lia.
    lia.
    lia.
    
    bvIntSimpl.
    bvIntSimpl.
    lia.
    bvIntSimpl.
    bvIntSimpl.

    (* When we subtract the new window from the scalar, it doesn't get too big*)
    rewrite sbvToInt_bvSub_equiv; try lia.
    rewrite sbvToInt_bvURem_equiv; try lia.
    rewrite bvToInt_shiftL_1_equiv; try lia.
    rewrite sbvToInt_shiftL_1_equiv; try lia.
    repeat rewrite Z.shiftl_1_l.
    split.
    apply Zorder.Zle_minus_le_0.
    rewrite <- (@Z.sub_0_r (bvToInt 384%nat n)).
    apply Z.sub_le_mono.
    rewrite Z.sub_0_r.
    apply Z.mod_le.
    apply bvToInt_nonneg.
    apply Z.pow_pos_nonneg; simpl; lia.
    apply Z.pow_nonneg; simpl; lia.
    apply sub_window_lt.
    lia.
    bvIntSimpl.
    bvIntSimpl.
    bvIntSimpl.
    bvIntSimpl.
    bvIntSimpl.
    
    rewrite sbvToInt_bvSub_equiv; try lia.
    bvIntSimpl.
    apply Z.lt_add_lt_sub_l.
    rewrite Z.add_opp_r.
    eapply Z.lt_le_trans.
    apply Z.lt_sub_0.
    eapply Z.pow_lt_mono_r; lia.
    eapply Z.mod_pos_bound.
    apply Z.pow_pos_nonneg; lia.
    bvIntSimpl.
    bvIntSimpl.
  
    lia.
    lia.
   
    rewrite H3.
    eapply IHnw.
    lia.
    
    apply bvToInt_shiftR_lt.
    lia.

    rewrite bvToInt_bvSub_small_equiv.

    rewrite sbvToInt_bvSub_equiv; try lia.
    rewrite sbvToInt_bvURem_equiv; try lia.
    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    rewrite bvToInt_shiftL_1_equiv; try lia.
    rewrite sbvToInt_shiftL_1_equiv; try lia.
    repeat rewrite Z.shiftl_1_l.
    replace (2 ^ (Z.of_nat wsize + Z.of_nat (S nw * wsize)))%Z with (2 ^ Z.of_nat (S (S nw) * wsize))%Z.
    apply sub_window_lt.
    lia.
    split.
    apply bvToInt_nonneg.
    eauto.
    simpl.
    lia.
    lia.
    (* 2 * 2 ^wsize is positive *)
    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    bvIntSimpl.
    lia.
   
    (* 2 * 2^wsize <= 2^383 *)
    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    bvIntSimpl.
    lia.

    rewrite sbvToInt_bvURem_equiv; try lia.
    split.
    eapply Z.le_trans.
    apply Z.opp_nonpos_nonneg.
    eapply Z.pow_nonneg; simpl; lia.
    apply Z.mod_pos_bound.
    (* 2 * 2 ^wsize is positive *)
    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    bvIntSimpl.
    lia.

    eapply Z.lt_le_trans.
    apply Z.mod_pos_bound.
    (* 2 * 2 ^wsize is positive *)
    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    bvIntSimpl.
    lia.

    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    eapply Z.pow_le_mono; simpl; lia.
    lia.
    lia.

    (* 2 * 2 ^wsize is positive *)
    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    bvIntSimpl.
    lia.

    (* 2 * 2^wsize < 2^384 *)
    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    bvIntSimpl.
    lia.

    rewrite bvToInt_sbvToInt_equiv.
    split.
    eapply Z.le_trans.
    apply Z.opp_nonpos_nonneg.
    eapply Z.pow_nonneg; simpl; lia.
    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    eapply Z.pow_nonneg; simpl; lia.
    lia.
    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    eapply Z.pow_lt_mono_r; simpl; lia.
    lia.
    lia.

    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    eapply Z.pow_lt_mono_r; simpl; lia.
    lia.

    (* by a similar argument to the one above, the difference fits in the original bit width. *)
    rewrite sbvToInt_bvSub_equiv; try lia.
    rewrite sbvToInt_bvURem_equiv; try lia.
    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    rewrite bvToInt_shiftL_1_equiv; try lia.
    rewrite sbvToInt_shiftL_1_equiv; try lia.
    repeat rewrite Z.shiftl_1_l.
    split.
    apply Zorder.Zle_minus_le_0.
    rewrite <- (@Z.sub_0_r (bvToInt 384%nat n)).
    apply Z.sub_le_mono.
    rewrite Z.sub_0_r.
    apply Z.mod_le.
    apply bvToInt_nonneg.
    apply Z.pow_pos_nonneg; simpl; lia.
    apply Z.pow_nonneg; simpl; lia.
    apply sub_window_lt.
    lia.
    split.
    apply bvToInt_nonneg.
    eauto.

    (* integers from 384 bit vectors are less than 2^384 *)
    bvIntSimpl.
    lia.

    (* 2 * 2 ^wsize is positive *)
    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    bvIntSimpl.
    lia.
    (* 2 * 2^wsize <= 2^383 *)
    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    bvIntSimpl.
    lia.

    rewrite sbvToInt_bvURem_equiv; try lia.
    split.
    eapply Z.le_trans.
    apply Z.opp_nonpos_nonneg.
    eapply Z.pow_nonneg; simpl; lia.
    apply Z.mod_pos_bound.
    (* 2 * 2 ^wsize is positive *)
    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    bvIntSimpl.
    lia.

    eapply Z.lt_le_trans.
    apply Z.mod_pos_bound.
    (* 2 * 2 ^wsize is positive *)
    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    bvIntSimpl.
    lia.

    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    eapply Z.pow_le_mono; simpl; lia.
    lia.
    lia.

    (* 2 * 2 ^wsize is positive *)
    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    bvIntSimpl.
    lia.

    (* 2 * 2^wsize < 2^384 *)
    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    bvIntSimpl.
    lia.

    rewrite bvToInt_sbvToInt_equiv.
    split.
    eapply Z.le_trans.
    apply Z.opp_nonpos_nonneg.
    eapply Z.pow_nonneg; simpl; lia.
    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    eapply Z.pow_nonneg; simpl; lia.
    lia.
    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    eapply Z.pow_lt_mono_r; simpl; lia.
    lia.
    lia.

    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    eapply Z.pow_lt_mono_r; simpl; lia.
    lia.

    rewrite sbvToInt_bvSub_equiv; try lia.
    bvIntSimpl.
    apply Z.lt_add_lt_sub_l.
    rewrite Z.add_opp_r.
    eapply Z.lt_le_trans.
    apply Z.lt_sub_0.
    eapply Z.pow_lt_mono_r; lia.
    eapply Z.mod_pos_bound.
    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    apply Z.pow_pos_nonneg; lia.
    lia.
    lia.
    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    apply Z.pow_pos_nonneg; lia.
    lia.
    lia.
    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    apply Z.pow_le_mono_r; lia.
    lia.
    lia.
    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    bvIntSimpl.
    lia.
    bvIntSimpl.
  Qed.

  Theorem mul_scalar_rwnaf_odd_abstract_equiv : forall nw wsize z,
    0 < wsize < 16 ->
    (bvToInt 384%nat z < 2 ^ Z.of_nat (S (S (S nw)) * wsize))%Z ->
    List.Forall2 (fun (x : Z) (y : bitvector 16) => x = (sbvToInt _ y))
  (recode_rwnaf_odd wsize (S (S nw)) (bvToInt _ z))
  (mul_scalar_rwnaf_odd_abstract wsize nw z).

    intros.
    eapply (@forall2_trans  _ _ _ _ (eq)).
    apply (recode_rwnaf_odd_bv_equiv).
    lia.
    lia.
    intros; subst.
    trivial.
    intros; subst; trivial.
    apply forall2_eq.

    unfold mul_scalar_rwnaf_odd_abstract.
  
    rewrite (@scanl_fix_equiv (bitvector 16 * bitvector 384) Integer (bitvector 16) (inhabitant
            (Inhabited_prod (bitvector 16)
               (bitvector 384)))
      (fun p =>
         mul_scalar_rwnaf_odd_loop_body_abstract wsize (snd p))
      (toN_int nw)
      (S nw)
      (fun (p : bitvector 16 * bitvector 384) => fst p) 
      (fun p => drop _ 368 16 (snd p))
      (mul_scalar_rwnaf_odd_loop_body_abstract wsize z)); intros.

    rewrite recode_rwnaf_odd_bv_scanl_equiv.
    reflexivity.
    lia.

    apply toN_int_length.
    
  Qed.

  Definition conditional_subtract_if_even := conditional_subtract_if_even Fsquare Fadd Fsub Fmul Fopp.
  Definition point_opp := (point_opp Fopp).

  Theorem conditional_subtract_if_even_jac_eq_ite : forall n p1 p2,
    jac_eq (seqToProd (EC_P384_5.conditional_subtract_if_even Fsquare Fmul Fsub Fadd
        Fopp p1 n p2)) (seqToProd (if (Nat.even (bvToNat _ n)) then (point_add false p1 (point_opp p2)) else p1)).
  
    intros.
    rewrite conditional_subtract_if_even_equiv.
    eapply jac_eq_refl.
  Qed.

  Theorem point_opp_equiv : forall p,
    jac_eq 
    (fromPoint (Jacobian.opp p))
    (seqToProd (point_opp (prodToSeq (fromPoint p)))).

    intros.
    unfold point_opp. simpl.
    unfold seqToProd, prodToSeq, nth_order. simpl.
    destruct p. simpl.
    destruct x. simpl.
    destruct p. 
    apply jac_eq_refl.
  Qed.
  
  Ltac destructVec := repeat (match goal with
    | [H : exists _, _ |- _ ] => destruct H
    | [p : seq _ _ |- _ ] => unfold seq in p; simpl in p
    | [p : Vec _ _ |- _ ] => unfold Vec in *
    | [p : t _ _ |- _ ] => destruct (Vec_S_cons _ _ p)
    | [p : t _ _ |- _ ] => rewrite (@Vec_0_nil _ p) in *; clear p
    end; subst).

  Theorem point_opp_jac_eq_proper : forall p1 p2,
    jac_eq (seqToProd p1) (seqToProd p2) ->
    jac_eq 
      (seqToProd (point_opp p1))
       (seqToProd (point_opp p2)).

    intros.
    unfold point_opp, EC_P384_Abstract.point_opp.
    unfold jac_eq in *.
    destructVec.
    simpl in *.
    unfold nth_order in *.
    simpl in *.
    repeat erewrite sawAt_nth_equiv; try lia.
    simpl.
    destruct (dec (Feq x4 0)).
    trivial.
    intuition idtac.
    nsatz.

  Qed.

  Theorem map_bvAdd_0 : forall n ls,
    (List.map (bvAdd n (bvNat n 0%nat)) ls) = ls.

    induction ls; intros; simpl in *.
    reflexivity.
    rewrite IHls.
    f_equal.
    apply bvAdd_id_l.

  Qed.

  Theorem felem_cmovznz_equiv : forall x y z,
    felem_cmovznz x y z = if (bvEq _ x (intToBv 64 0)) then y else z.

    intros.
    reflexivity.

  Qed.

  Theorem toN_excl_bv_length: forall n x,
    List.length (toN_excl_bv n x) = x.

    induction x; intros; simpl in *.
    trivial.
    rewrite app_length.
    rewrite IHx.
    simpl.
    lia.

  Qed.

  Theorem bvXor_bvEq : forall n y w,
    bvEq n (bvXor _ y w) (intToBv _ 0)  = bvEq _ y w.
  
    induction n; intros; simpl in *.
    reflexivity.
    destruct (@Vec_S_cons _ _  y). destruct H.
    destruct (@Vec_S_cons _ _ w). destruct H0. 
    subst.
    rewrite bvXor_cons.
    rewrite intToBv_0_S.
    repeat rewrite bvEq_cons.
    destruct x; destruct x1; simpl; trivial.

  Qed.

  Theorem select_point_loop_body_equiv : forall w x y z,
    select_point_loop_body w x y z = 
       if (bvEq _ y w) then z else x.

    intros. 
    unfold select_point_loop_body.
    simpl.
    unfold ecXor.
    simpl.
    repeat rewrite felem_cmovznz_equiv.
    case_eq (bvEq 64 (bvXor 64 y w) (intToBv 64 0)); intros;
    rewrite sawAt_3_equiv;
    case_eq (bvEq _ y w); intros; 
    trivial;
    rewrite bvXor_bvEq in H; 
    congruence.

  Qed.

  Theorem select_point_abstract_nth_equiv_h : forall ls n a,
    (Z.of_nat (List.length ls) < 2^64 )%Z ->
     (Z.of_nat n < 2^64 )%Z ->
    List.fold_left
      (fun (acc : seq 3 (seq 6 (seq 64 Bool)))
         (p : seq 64 Bool * seq 3 (seq 6 (seq 64 Bool))) =>
       select_point_loop_body (bvNat 64 (a + n)%nat) acc (fst p) (snd p))
      (combine (List.map (bvAdd _ (bvNat _ a)) (toN_excl_bv 64 (Datatypes.length ls))) ls)
      (of_list [zero_felem; zero_felem; zero_felem]) =
    List.nth n ls (cons F 0 2 (cons F 0 1 (cons F 0 0 (nil F)))).

    induction ls using rev_ind; intros; simpl in *.
    destruct n; reflexivity.
    rewrite app_length.
    simpl.
    rewrite PeanoNat.Nat.add_1_r.
    simpl.
    rewrite map_app.
    rewrite combine_app_eq.
    rewrite fold_left_app.
    rewrite IHls.
    simpl.
    rewrite select_point_loop_body_equiv.
    case_eq (bvEq 64 (bvAdd 64 (intToBv 64 (Z.of_nat a0)) (intToBv 64 (Z.of_nat (Datatypes.length ls))))
    (intToBv 64 (Z.of_nat (a0 + n)))); intros.
    assert (List.length ls = n). (* because list length and n are small*)
    apply bvEq_eq in H1.
    rewrite Znat.Nat2Z.inj_add in H1.

    rewrite intToBv_add_equiv in H1.
    apply bvAdd_same_l_if in H1.
    apply intToBv_eq_pos in H1.
    lia.
    intuition idtac.
    lia.
    rewrite app_length in H.
    lia.
    lia.

    rewrite app_nth2.
    subst.
    rewrite PeanoNat.Nat.sub_diag.
    reflexivity.
    lia.

    destruct (Compare_dec.lt_eq_lt_dec n (List.length ls)). 
    destruct s.
    rewrite app_nth1.
    reflexivity.
    lia.

    subst.
    (* contradiction *)
    rewrite Znat.Nat2Z.inj_add in H1.
    rewrite intToBv_add_equiv in H1.
    rewrite bvEq_refl in H1.
    discriminate.

    rewrite app_nth2.
    repeat rewrite nth_overflow.
    reflexivity.
    simpl.
    lia.
    lia.
    lia.
    rewrite app_length in H.
    lia.
    trivial.
    rewrite map_length.
    rewrite toN_excl_bv_length.
    reflexivity.

  Qed.

  Theorem select_point_abstract_nth_equiv : forall x ls,
    (Z.of_nat (Datatypes.length ls) < 2 ^ 64)%Z ->
    (Z.of_nat (bvToNat 64%nat x) < 2 ^ 64)%Z ->
    select_point_abstract x ls = List.nth (bvToNat _ x) ls (cons _ Fzero _ (cons _ Fzero _ (cons _ Fzero _ (nil _)))).

    intros.
    rewrite <- (bvNat_bvToNat_id _ x) at 1.
    unfold select_point_abstract.
    specialize (select_point_abstract_nth_equiv_h ls (bvToNat 64 x) 0); intros.
    rewrite map_bvAdd_0 in H1.
    apply H1.
    trivial.
    trivial.
  Qed.

  Theorem sawAt_2_equiv : forall A (inh : Inhabited A) (v : Vector.t A 2),
  Vector.cons _ (sawAt 2%nat A v 0%nat) _
    (Vector.cons _ (sawAt 2%nat A v 1%nat) _ (Vector.nil A))
    = v.

    intros.
    destruct (Vec_S_cons _ _ v). destruct H. subst.
    destruct (Vec_S_cons _ _ x0). destruct H. subst.
    repeat rewrite sawAt_nth_equiv; try lia.
    repeat rewrite to_list_cons.
    simpl.
    specialize (Vec_0_nil _ x2); intros; subst.
    reflexivity.

  Qed.

  Theorem select_point_affine_loop_body_equiv : forall w x y z,
    select_point_affine_loop_body w x y z = 
       if (bvEq _ y w) then z else x.

    intros. 
    unfold select_point_affine_loop_body.
    simpl.
    unfold ecXor.
    simpl.
    repeat rewrite felem_cmovznz_equiv.
    case_eq (bvEq 64 (bvXor 64 y w) (intToBv 64 0)); intros;
    rewrite sawAt_2_equiv;
    case_eq (bvEq _ y w); intros; 
    trivial;
    rewrite bvXor_bvEq in H; 
    congruence.

  Qed.

  Theorem select_point_affine_abstract_nth_equiv_h : forall ls n a,
    (Z.of_nat (List.length ls) < 2^64 )%Z ->
     (Z.of_nat n < 2^64 )%Z ->
    List.fold_left
      (fun acc p =>
       select_point_affine_loop_body (bvNat 64 (a + n)%nat) acc (fst p) (snd p))
      (combine (List.map (bvAdd _ (bvNat _ a)) (toN_excl_bv 64 (Datatypes.length ls))) ls)
      (of_list [zero_felem; zero_felem]) =
    List.nth n ls (cons F 0 1 (cons F 0 0 (nil F))).

    induction ls using rev_ind; intros; simpl in *.
    destruct n; reflexivity.
    rewrite app_length.
    simpl.
    rewrite PeanoNat.Nat.add_1_r.
    simpl.
    rewrite map_app.
    rewrite combine_app_eq.
    rewrite fold_left_app.
    rewrite IHls.
    simpl.
    rewrite select_point_affine_loop_body_equiv.
    case_eq (bvEq 64 (bvAdd 64 (intToBv 64 (Z.of_nat a0)) (intToBv 64 (Z.of_nat (Datatypes.length ls))))
    (intToBv 64 (Z.of_nat (a0 + n)))); intros.
    assert (List.length ls = n). (* because list length and n are small*)
    apply bvEq_eq in H1.
    rewrite Znat.Nat2Z.inj_add in H1.

    rewrite intToBv_add_equiv in H1.
    apply bvAdd_same_l_if in H1.
    apply intToBv_eq_pos in H1.
    lia.
    intuition idtac.
    lia.
    rewrite app_length in H.
    lia.
    lia.

    rewrite app_nth2.
    subst.
    rewrite PeanoNat.Nat.sub_diag.
    reflexivity.
    lia.

    destruct (Compare_dec.lt_eq_lt_dec n (List.length ls)). 
    destruct s.
    rewrite app_nth1.
    reflexivity.
    lia.

    subst.
    (* contradiction *)
    rewrite Znat.Nat2Z.inj_add in H1.
    rewrite intToBv_add_equiv in H1.
    rewrite bvEq_refl in H1.
    discriminate.

    rewrite app_nth2.
    repeat rewrite nth_overflow.
    reflexivity.
    simpl.
    lia.
    lia.
    lia.
    rewrite app_length in H.
    lia.
    trivial.
    rewrite map_length.
    rewrite toN_excl_bv_length.
    reflexivity.

  Qed.

  Theorem select_point_affine_abstract_nth_equiv : forall x ls,
    (Z.of_nat (Datatypes.length ls) < 2 ^ 64)%Z ->
    (Z.of_nat (bvToNat 64%nat x) < 2 ^ 64)%Z ->
    select_point_affine_abstract x ls = List.nth (bvToNat _ x) ls (cons _ Fzero _ (cons _ Fzero _ (nil _))).

    intros.
    rewrite <- (bvNat_bvToNat_id _ x) at 1.
    unfold select_point_affine_abstract.
    specialize (select_point_affine_abstract_nth_equiv_h ls (bvToNat 64 x) 0); intros.
    rewrite map_bvAdd_0 in H1.
    apply H1.
    trivial.
    trivial.
  Qed.

  Definition pre_comp_table_abstract := pre_comp_table_abstract Fsquare Fmul Fsub Fadd.

  Theorem preCompTable_equiv_h : forall ls1 ls2 p1 p2,
    List.length ls1 = List.length ls2 ->
    jac_eq (fromPoint p1) (seqToProd p2) ->
    List.Forall2
  (fun (a0 : point) (b0 : seq 3 F) =>
   jac_eq (fromPoint a0) (seqToProd b0))
  (CryptolToCoq_equiv.scanl
     (fun (a0 : Jacobian.point) (_ : nat) =>
      Jacobian.add (Jacobian.double p1) a0)
     ls1 p1)
  (CryptolToCoq_equiv.scanl
     (fun (z : seq 3 (seq 6 (seq 64 Bool)))
        (_ : Integer) =>
      EC_P384_5.point_add Fsquare Fmul
        Fsub Fadd
        (ecNumber 0%nat Bool PLiteralBit)
        (EC_P384_5.point_double Fsquare
           Fmul Fsub Fadd
           p2) z)
     ls2 p2).

    intros.
    eapply (@Forall2_scanl _ _ _ _ _ (fun x y => True)); intros.
    eapply Forall2_I; eauto.
    eapply point_add_jac_eq.

    assert (exists p2', p2 = prodToSeq (fromPoint p2')).
    apply jac_eq_point_ex in H0.
    destruct H0.
    exists x.
    rewrite <- H0.
    rewrite prodToSeq_inv.
    reflexivity.

    destruct H3.
    subst.
    rewrite <- double_eq_minus_3.
    rewrite seqToProd_inv in H0.
    rewrite seqToProd_inv.
    eapply jac_eq_trans.
    apply jacobian_eq_jac_eq.
    apply Jacobian.Proper_double.
    eapply jac_eq_jacobian_eq.
    eauto.
    apply Jacobian.double_minus_3_eq_double.
    trivial.
    trivial.
  Qed.

  Theorem preCompTable_equiv : forall w p,
    (tableSize w) > 1 ->
    List.Forall2 (fun a b => jac_eq (fromPoint a) (seqToProd b))
      (preCompTable w p)
      (pre_comp_table_abstract (Nat.pred (Nat.pred (tableSize w))) (prodToSeq (fromPoint p))).

    intros.
    unfold preCompTable, GroupMulWNAF.preCompTable, preCompTable_h, pre_comp_table_abstract, EC_P384_Abstract.pre_comp_table_abstract.
    rewrite (@fold_left_scanl_equiv _ _ _ (fun a b => (groupAdd (groupDouble p) a))).
    eapply preCompTable_equiv_h.
    rewrite forNats_length.
    rewrite map_length.
    rewrite toN_int_length.
    lia.
    rewrite seqToProd_inv.
    eapply jac_eq_refl.
  Qed.

  Local Opaque shiftR.

  Theorem ct_abs_equiv : forall  b1 b2,
    (Z.opp (Z.pow 2 (Z.of_nat 15)) < b1)%Z ->
    b1 = sbvToInt 16 b2 ->
    sbvToInt 16 (bvAdd 16 (shiftR 16 bool false b2 15) (bvXor 16 b2 (bvSShr 15 b2 15))) 
    =
    Z.abs b1.

    intros.
    subst.
    remember (shiftR 16 bool false b2 15) as is_neg.
    case_eq (sbvToInt 16 b2); intros; simpl in *.

    (* zero *)
    apply sbvToInt_0_replicate in H0.
    subst.
    rewrite bvXor_comm.
    rewrite bvXor_zero.
    rewrite shiftR_false_0.
    rewrite bvAdd_replicate_0.
    apply sbvToInt_replicate_0.

    (* positive *)
    simpl.
    rewrite shiftR_all_nonneg in Heqis_neg.
    rewrite Heqis_neg.
    rewrite bvAdd_replicate_0.
    rewrite bvSShr_all_nonneg.
    rewrite bvXor_zero. 
    trivial.
    lia.
    lia.
    lia.

    (* negative *)
    rewrite shiftR_all_neg in Heqis_neg.
    rewrite Heqis_neg.
    rewrite bvSShr_all_neg.
    rewrite bvAdd_comm.
    rewrite twos_complement_equiv.
    rewrite H0.
    apply Pos2Z.opp_neg.
    lia.
    simpl in *.
    lia.
    lia.
    lia.
    lia.
  Qed.

  Theorem groupDouble_n_double_comm_jac : forall n a1,
    Jacobian.eq (Jacobian.double (groupDouble_n n a1)) (groupDouble_n n (groupDouble a1)).

    induction n; intros; simpl in *.
    reflexivity.
    apply Jacobian.Proper_double.
    eapply IHn.
  
  Qed.

  Theorem groupDouble_n_fold_left_double_equiv : forall ws ls a1 a2,
    List.length ls = ws ->
    jac_eq (fromPoint a1) (seqToProd a2) ->
    jac_eq 
  (fromPoint (groupDouble_n ws a1))
  (seqToProd
     (List.fold_left
        (fun (x : seq 3 (seq 6 (seq 64 Bool))) (_ : Integer)
         =>
         EC_P384_5.point_double Fsquare Fmul Fsub
           Fadd x) ls a2)).

    induction ws; destruct ls; intros; simpl in *; try lia.
    trivial.
    eapply jac_eq_trans; [idtac | eapply IHws].
    apply jacobian_eq_jac_eq.
    eapply groupDouble_n_double_comm_jac.
    lia.
    assert (exists a2', (seqToProd a2) = (fromPoint a2')).
    eapply jac_eq_point_ex; eauto.
    destruct H1. subst.
    replace a2 with (prodToSeq (fromPoint x)).
    rewrite <- double_eq_minus_3.
    rewrite seqToProd_inv.
    apply jacobian_eq_jac_eq.
    transitivity (Jacobian.double x).
    apply Jacobian.Proper_double.
    eapply jac_eq_jacobian_eq.
    eapply jac_eq_trans; eauto.
    eapply jac_eq_refl_abstract.
    trivial.

    eapply Jacobian.double_minus_3_eq_double.
    rewrite <- H1.
    apply prodToSeq_inv.
 
  Qed.

  Definition point_opp_prod (p : F * F * F) : F * F * F :=
    ((fst (fst p), Fopp (snd (fst p))), snd p).

  Theorem jac_eq_opp : forall p1 p2,
    jac_eq p1 p2 ->
    jac_eq (point_opp_prod p1) (point_opp_prod p2).

    intros.
    unfold jac_eq, point_opp_prod in *.
    destruct p1. destruct p.
    destruct p2. destruct p.
    simpl in *.
    destruct (dec (Feq f 0)); trivial.
    intuition idtac.
    rewrite opp_mul_eq.
    rewrite <- associative.
    symmetry.
    rewrite opp_mul_eq.
    rewrite <- associative.
    symmetry.
    apply fmul_same_l.
    trivial.
 
  Qed.

  Theorem point_opp_prod_equiv : forall p,
    (seqToProd (point_opp (prodToSeq p))) = point_opp_prod p.

    intros.
    reflexivity.

  Qed.


  Theorem conditional_point_opp_equiv : forall x p1 p2,
    jac_eq (fromPoint p1) (seqToProd p2) ->
    jac_eq
  (seqToProd
     (conditional_point_opp Fopp x p2))
  (fromPoint (if (dec ((sbvToInt _ x) = 0%Z)) then p1 else (Jacobian.opp p1))).

    intros.
    unfold conditional_point_opp.
    rewrite felem_cmovznz_equiv.
    destruct (dec (sbvToInt 64 x = 0%Z)); intros.
    apply sbvToInt_0_replicate in e.
    subst.
    rewrite rep_false_eq_int_bv.
    rewrite bvEq_refl.
    rewrite sawAt_3_equiv.
    apply jac_eq_symm.
    trivial.

    case_eq (bvEq 64 x (intToBv 64 0)); intros.
    apply bvEq_eq in H0.
    rewrite intToBv_0_eq_replicate in H0.
    subst.
    rewrite sbvToInt_replicate_0 in n.
    intuition idtac.
    eapply jac_eq_symm.
    eapply jac_eq_trans.
    apply point_opp_equiv.
    rewrite point_opp_prod_equiv.
    eapply jac_eq_trans.
    eapply jac_eq_opp; eauto.
    eapply jac_eq_symm.
    eapply jac_eq_refl_abstract.
    unfold seqToProd, point_opp; simpl.
    
    repeat match goal with 
    | [|- context[nth_order (cons ?A ?x ?n ?v) ?pf]] =>
      rewrite (@nth_order_0_cons A x n v)
    | [|- context[nth_order (cons ?A ?x ?n ?v) ?pf]] =>
      erewrite (@nth_order_S_cons A x n v)
    end.

     repeat erewrite sawAt_nth_order_equiv.
    reflexivity.

    Unshelve.
    lia.
    lia.
    lia.
    lia.
    lia.
    lia.

  Qed.

  Theorem conditional_point_opp_ifso_equiv : forall x p1 p2,
    sbvToInt _ x <> 0%Z ->
    jac_eq (fromPoint p1) (seqToProd p2) ->
    jac_eq
  (seqToProd
     (conditional_point_opp Fopp x p2))
  (fromPoint (Jacobian.opp p1)).

    intros.
    eapply jac_eq_trans.
    eapply conditional_point_opp_equiv; eauto.
    destruct (dec (sbvToInt 64 x = 0%Z)).
    congruence.
    apply jac_eq_refl.

  Qed.

  Theorem conditional_point_opp_ifnot_equiv : forall x p1 p2,
    sbvToInt _ x = 0%Z ->
    jac_eq (fromPoint p1) (seqToProd p2) ->
    jac_eq
  (seqToProd
     (conditional_point_opp Fopp x p2))
  (fromPoint p1).

    intros.
    eapply jac_eq_trans.
    eapply conditional_point_opp_equiv; eauto.
    destruct (dec (sbvToInt 64 x = 0%Z)).
    apply jac_eq_refl.
    congruence.

  Qed.
       
  Theorem sbvToInt_sign_extend_16_64_equiv : forall x,
    sbvToInt _ (sign_extend_16_64 x) = sbvToInt _ x.

    intros.
    unfold sign_extend_16_64.
    simpl.
    apply (@sbvToInt_sign_extend_equiv 16 48).
    lia.

  Qed.

  Theorem mul_body_equiv : forall pred_wsize p a1 a2 b1 b2,
    0 < pred_wsize < 15 ->
    jac_eq (fromPoint a1) (seqToProd a2) ->
    b1 = sbvToInt 16 b2 ->
    (- 2 ^ Z.of_nat (S pred_wsize) < b1 < 2 ^ Z.of_nat (S pred_wsize))%Z ->
    jac_eq
      (fromPoint
         (groupMul_signedWindows_fold_body
            (S pred_wsize)
            (fun x : Z =>
             if (x <? 0)%Z
             then
              Jacobian.opp
                (List.nth
                   (BinInt.Z.to_nat (BinInt.Z.shiftr (BinInt.Z.abs x) 1))
                   (preCompTable
                      (S pred_wsize) p) zero_point)
             else
              List.nth
                (BinInt.Z.to_nat (BinInt.Z.shiftr (BinInt.Z.abs x) 1))
                (preCompTable
                   (S pred_wsize) p) zero_point) a1 b1))
      (seqToProd
         (double_add_body_abstract Fsquare Fmul Fsub Fadd Fopp pred_wsize
            (EC_P384_Abstract.pre_comp_table_abstract Fsquare Fmul Fsub
               Fadd (Nat.pred (Nat.pred (tableSize (S pred_wsize))))
               (prodToSeq (fromPoint p))) a2 b2)).

    intros.
    unfold double_add_body_abstract.

    rewrite (select_point_abstract_nth_equiv).
    unfold groupMul_signedWindows_fold_body.
    unfold groupAdd_signedWindow.
    match goal with
    | [|- context[if ?a then _ else _]] =>
      case_eq a; intros
    end.
    eapply jac_eq_trans.
    apply jacobian_eq_jac_eq.
    apply jac_add_comm.
    eapply point_add_jac_eq.
    eapply groupDouble_n_fold_left_double_equiv.
    apply toN_int_length.
    trivial.
    
    subst.
    apply Z.ltb_lt in H3.
    eapply jac_eq_symm.
    eapply conditional_point_opp_ifso_equiv.
    unfold point_id_to_limb.
    removeCoerce.
    simpl.
    
    assert (63 < 64)%nat by lia.
    eapply (sbvToInt_nz_nth _ H1).
    assert (15 < 16) by lia.
    erewrite (@nth_order_append_eq Bool _ 16 _ 48 (intToBv 48 0) 15 H1 H4).
    repeat rewrite shiftR1_eq.
    repeat rewrite shiftR_shiftR_eq.
    assert (0 < 16) by lia.
    rewrite (@nth_order_shiftR_all_eq bool 15 16 _ H4 H5); intros.
    apply sbvToInt_neg_sign_bit_set.
    lia.

    match goal with
    | [|- jac_eq (fromPoint (List.nth ?a _ _)) (seqToProd (List.nth ?b _ _))] =>
      replace a with b
    end.
    eapply (@Forall2_nth_lt _ _ (fun a b => jac_eq (fromPoint a) (seqToProd b))).
    apply preCompTable_equiv.
    unfold tableSize.
    simpl.
    rewrite NPeano.Nat.sub_0_r.
    apply nat_shiftl_gt_base; lia.
    
    rewrite (@bvToNat_Z_to_nat_equiv _ _ (Z.div2 (Z.abs (sbvToInt _ b2)))).
    rewrite tableSize_correct.
    unfold tableSize.
    simpl.
    rewrite PeanoNat.Nat.sub_0_r.
    replace (Nat.shiftl 1 pred_wsize) with (Z.to_nat (2^(Z.of_nat pred_wsize))).
    apply Znat.Z2Nat.inj_lt.
    apply Z.div2_nonneg.
    lia.
    apply Z.pow_nonneg; lia.
    apply div2_lt.
    rewrite <- Z.pow_succ_r.
    apply Z.abs_lt.
    rewrite <- Znat.Nat2Z.inj_succ.
    trivial.
    lia.
    rewrite shiftl_to_nat_eq.
    rewrite Z.shiftl_1_l.
    reflexivity.
    lia.
    apply Z.div2_nonneg.
    lia.
    
    rewrite sbvToInt_sign_extend_16_64_equiv.
    erewrite bvSShr_Z_shiftr_equiv; [idtac | idtac | erewrite ct_abs_equiv]; eauto.
    rewrite Z.div2_spec.
    reflexivity.

    eapply Z.le_lt_trans.
    apply (@Z.opp_le_mono (2 ^ Z.of_nat (S pred_wsize))).
    apply Z.pow_le_mono.
    lia.
    lia.
    lia.

    rewrite (@bvToNat_Z_to_nat_equiv _ _ (Z.div2 (Z.abs (sbvToInt _ b2)))).
    rewrite Z.div2_spec.
    reflexivity.
    apply Z.div2_nonneg.
    lia.

    rewrite sbvToInt_sign_extend_16_64_equiv.
    erewrite bvSShr_Z_shiftr_equiv; [idtac | idtac | erewrite ct_abs_equiv]; eauto.
    rewrite Z.div2_spec.
    reflexivity.

    eapply Z.le_lt_trans.
    apply (@Z.opp_le_mono (2 ^ Z.of_nat (S pred_wsize))).
    apply Z.pow_le_mono.
    lia.
    lia.
    lia.

    eapply jac_eq_trans.
    apply jacobian_eq_jac_eq.
    apply jac_add_comm.
    eapply point_add_jac_eq.
    eapply groupDouble_n_fold_left_double_equiv.
    apply toN_int_length.
    trivial.
    
    subst.
    apply Z.ltb_ge in H3.
    eapply jac_eq_symm.
    eapply conditional_point_opp_ifnot_equiv.
    unfold point_id_to_limb.
    removeCoerce.
    simpl.
    
    (* shiftR produces all 0 *)
    rewrite shiftR_all_nonneg; trivial.
    lia.

    match goal with
    | [|- jac_eq (fromPoint (List.nth ?a _ _)) (seqToProd (List.nth ?b _ _))] =>
      replace a with b
    end.
    eapply (@Forall2_nth_lt _ _ (fun a b => jac_eq (fromPoint a) (seqToProd b))).
    apply preCompTable_equiv.
    apply nat_shiftl_gt_base;
    lia.
    
    rewrite (@bvToNat_Z_to_nat_equiv _ _ (Z.div2 (Z.abs (sbvToInt _ b2)))).
    rewrite Z.div2_spec.
    rewrite tableSize_correct.
    unfold tableSize.
    apply shiftr_window_small_Z.
    lia.
    intuition idtac.
    lia.
    apply Z.abs_lt.
    intuition idtac.
    lia.
    apply Z.div2_nonneg.
    lia.

    rewrite sbvToInt_sign_extend_16_64_equiv.
    erewrite bvSShr_Z_shiftr_equiv; [idtac | idtac | erewrite ct_abs_equiv]; eauto.
    rewrite Z.div2_spec.
    reflexivity.

    eapply Z.le_lt_trans.
    apply (@Z.opp_le_mono (2 ^ Z.of_nat (S pred_wsize))).
    apply Z.pow_le_mono.
    lia.
    lia.
    lia.

    eapply bvToNat_Z_to_nat_equiv.
    apply Z.shiftr_nonneg.
    apply Z.abs_nonneg.
    rewrite sbvToInt_sign_extend_16_64_equiv.
    apply bvSShr_Z_shiftr_equiv.
    trivial.
    apply ct_abs_equiv.
    eapply Z.le_lt_trans.
    apply (@Z.opp_le_mono (2 ^ Z.of_nat (S pred_wsize))).
    apply Z.pow_le_mono.
    lia.
    lia.
    lia.
    reflexivity.

    erewrite <- Forall2_length; [idtac | eapply preCompTable_equiv].
    rewrite tableSize_correct.
    unfold tableSize.
    rewrite shiftl_to_nat_eq.
    rewrite Z.shiftl_1_l.
    rewrite ZifyInst.of_nat_to_nat_eq.
    rewrite Z.max_r.
    apply Z.pow_lt_mono_r;
    lia.
    apply Z.pow_nonneg; lia.
    lia.
    unfold tableSize.
    apply nat_shiftl_gt_base.
    lia.
    lia.

    apply bvToNat_lt_word.

  Qed.


  Theorem scanl_head : forall (A B : Type)(f : A -> B -> A)ls acc def,
      List.hd def (CryptolToCoq_equiv.scanl f ls acc) = acc.

    intros.
    destruct ls; reflexivity.

  Qed.


  Theorem pre_comp_table_abstract_nth_0  : forall wsize p def,
    List.nth 0 (EC_P384_Abstract.pre_comp_table_abstract Fsquare Fmul
              Fsub Fadd (Nat.pred (Nat.pred (tableSize wsize)))
              p) def = p.
  
    intros.
    unfold EC_P384_Abstract.pre_comp_table_abstract.
    rewrite nth_0_hd_equiv.
    apply scanl_head.

  Qed.

  Definition point_mul_abstract := point_mul_abstract Fsquare Fmul Fsub Fadd Fopp.

  Section PointMulAbstract.
  Variable wsize : nat.
  Hypothesis wsize_range : (1 < wsize < 16)%nat.
  Variable nw : nat.
  Hypothesis nw_range : nw <> 0%nat.

  Theorem mul_scalar_rwnaf_abstract_equiv : forall z,
    (bvToInt 384%nat z < 2 ^ Z.of_nat (S (S (S nw)) * wsize))%Z ->
    List.Forall2 (fun x (y : bitvector 16) => x = (sbvToInt _ y))
    (recode_rwnaf wsize (S (S (S nw))) (bvToInt _ z)) 
    (mul_scalar_rwnaf_abstract wsize nw z).

    intros. 
    unfold recode_rwnaf, mul_scalar_rwnaf_abstract.
    replace (BinInt.Z.lor (bvToInt 384 z) 1) with
      (bvToInt _ (bvOr 384 z (intToBv 384 1))).
    apply mul_scalar_rwnaf_odd_abstract_equiv.
    lia.
  
    rewrite bvOr_bvToInt_equiv.
    rewrite bvToInt_intToBv_id.
    case_eq (BinInt.Z.odd (bvToInt 384%nat z)); intros.
    rewrite Z_odd_lor_1; eauto.
    rewrite Z_even_lor_1.

    assert (Z.even (2 ^ Z.of_nat (S (S (S nw)) * wsize)) = true)%Z.
    rewrite Z.even_pow.
    trivial.
    lia.
    assert (Z.odd (BinInt.Z.succ (bvToInt 384%nat z)) = true).
    rewrite Z.odd_succ.
    rewrite Zeven.Zeven_odd_bool.
    rewrite H0.
    trivial.
    assert (BinInt.Z.succ (bvToInt 384%nat z) <> 2 ^ Z.of_nat (S (S (S nw)) * wsize))%Z.
    intuition idtac.
    rewrite H3 in H2.
    rewrite <- Z.negb_even in H2.
    rewrite Z.even_pow in H2.
    simpl in *.
    discriminate.
    lia.
    lia.
    rewrite <- Z.negb_odd.
    rewrite H0.
    trivial.
    lia.
    rewrite bvOr_bvToInt_equiv.
    rewrite bvToInt_intToBv_id.
    reflexivity.
    lia.

  Qed.

  Theorem groupDouble_n_zero : forall n,
    groupDouble_n n zero_point == zero_point.

    induction n; intros; simpl in *.
    reflexivity.
    transitivity (Jacobian.double zero_point).
    eapply Jacobian.Proper_double.
    eauto.
    rewrite jac_double_correct.
    rewrite jac_add_id_l.
    reflexivity.

  Qed.

  Theorem point_mul_abstract_signedRegular_cases : forall n p,
    (BinInt.Z.of_nat (bvToNat 384%nat n) <
   BinInt.Z.shiftl 1 (BinInt.Z.of_nat (S (S (S nw)) * wsize)))%Z->
      jac_eq
    (seqToProd
       (List.fold_left
          (double_add_body_abstract Fsquare Fmul Fsub Fadd Fopp (Nat.pred wsize)
             (EC_P384_Abstract.pre_comp_table_abstract Fsquare Fmul
                Fsub Fadd (Nat.pred (Nat.pred (tableSize wsize)))
                (prodToSeq (fromPoint p))))
          (skipn 1
             (List.rev (mul_scalar_rwnaf_abstract wsize nw n)))
          (select_point_abstract
             (sign_extend_16_64
                (bvSShr 15
                   (List.nth (S (S nw))
                      (mul_scalar_rwnaf_abstract wsize nw n)
                      (bvNat 16 0%nat)) 1))
             (EC_P384_Abstract.pre_comp_table_abstract Fsquare Fmul
                Fsub Fadd (Nat.pred (Nat.pred (tableSize wsize)))
                (prodToSeq (fromPoint p))))))
    (fromPoint
       (groupMul_signedWindows
          wsize
          (fun x : Z =>
           if (x <? 0)%Z
           then
            Jacobian.opp
              (List.nth
                 (BinInt.Z.to_nat (BinInt.Z.shiftr (BinInt.Z.abs x) 1))
                 (preCompTable
                    wsize p) zero_point)
           else
            List.nth
              (BinInt.Z.to_nat (BinInt.Z.shiftr (BinInt.Z.abs x) 1))
              (preCompTable
                 wsize p) zero_point)
          (recode_rwnaf wsize (S (S (S nw)))
             (BinInt.Z.of_nat (bvToNat 384 n))))).

    intros.
    eapply jac_eq_symm.
    rewrite groupMul_signedWindows_fold_equiv.
    rewrite (@fold_left_unroll_one _ _ 0%Z).
    eapply (@fold_left_R _ _ _ _ 
      (fun a1 a2 => jac_eq (fromPoint a1) (seqToProd a2))
      (fun b1 b2 => b1 = sbvToInt 16 b2)
    ).
    erewrite (@forall2_map_eq _ _
      (intToBv 16)
      
      (mul_scalar_rwnaf_abstract
                    wsize nw n)
      (recode_rwnaf wsize
                 (S (S (S nw)))
                 (BinInt.Z.of_nat
                    (bvToNat _ n)))
    ).
    replace (bvNat 16 0%nat) with (intToBv 16 0%Z).
    rewrite map_nth.

    rewrite select_point_abstract_nth_equiv.
    unfold groupMul_signedWindows_fold_body.
    unfold groupAdd_signedWindow.
    match goal with
    | [|- context[if ?a then _ else _]] =>
      case_eq a; intros
    end.
    exfalso.
    apply Z.ltb_lt in H0.
    match goal with
    | [H: (?a < 0)%Z |- _] =>
      assert (0 <= a)%Z
    end.
    rewrite hd_rev_eq_last.
    apply recode_rwnaf_last_nonneg.
    lia.
    lia.
    trivial.
    lia.
    
    rewrite Z.abs_eq.

    eapply (@jac_eq_trans _ 
      (fromPoint (List.nth
           (BinInt.Z.to_nat
              (BinInt.Z.shiftr
                    (List.hd 0%Z
                       (List.rev
                          (recode_rwnaf wsize
                             (S (S (S nw)))
                             (BinInt.Z.of_nat (bvToNat 384 n)))))
                 1))
           (preCompTable
              wsize p) zero_point)
    )).
    eapply jacobian_eq_jac_eq.
    transitivity 
      (Jacobian.add
     (List.nth
        (BinInt.Z.to_nat
           (BinInt.Z.shiftr
                 (List.hd 0%Z
                    (List.rev
                       (recode_rwnaf wsize
                          (S (S (S nw)))
                          (BinInt.Z.of_nat (bvToNat 384 n)))))
              1))
        (preCompTable
           wsize p) zero_point)
     (zero_point)).
    
    eapply Jacobian.Proper_add. 
    reflexivity.
    apply (@groupDouble_n_zero wsize).
    rewrite jac_add_comm.
    apply jac_add_id_l.
    rewrite hd_rev_eq_last.
    rewrite last_nth_equiv.
    rewrite recode_rwnaf_length.
    match goal with 
    | [|- jac_eq (fromPoint (List.nth ?a _ _ )) (seqToProd (List.nth ?b _ _ ))] =>  
      replace a with b
    end.
    eapply (@Forall2_nth_lt _ _ (fun a b => jac_eq (fromPoint a) (seqToProd b))).
    apply preCompTable_equiv.
    unfold tableSize.
    apply nat_shiftl_gt_base.
    lia.
    lia.
    (* The last window is always non-negative*)
    rewrite (@bvToNat_Z_to_nat_equiv _ _ (Z.div2 (List.nth (S (S nw))
              (recode_rwnaf wsize (S (S (S nw))) (BinInt.Z.of_nat (bvToNat 384 n))) 0%Z))).
    rewrite tableSize_correct.
    unfold tableSize.
    rewrite shiftl_to_nat_eq.
    apply Znat.Z2Nat.inj_lt.
    apply Z.div2_nonneg.
    replace (S (S nw)) with (Nat.pred (List.length (recode_rwnaf wsize (S (S (S nw))) (BinInt.Z.of_nat (bvToNat 384%nat n))) )) at 1.
    rewrite <- last_nth_equiv.
    rewrite <- hd_rev_eq_last.
    apply Z.ltb_ge; eauto.
    rewrite recode_rwnaf_length.
    lia.
    lia.
    lia.
    apply Z.shiftl_nonneg; lia.

    apply div2_lt.
    rewrite Z.shiftl_1_l.
    rewrite <- Z.pow_succ_r.
    rewrite <- Znat.Nat2Z.inj_succ.
    replace (S (wsize - 1)) with wsize.
    apply recode_rwnaf_bound_nth; try lia.
    lia.
    lia.
    lia.

    apply Z.div2_nonneg.
    replace (S (S nw)) with (Nat.pred (List.length (recode_rwnaf wsize (S (S (S nw))) (BinInt.Z.of_nat (bvToNat 384%nat n))) )) at 1.
    rewrite <- last_nth_equiv.
    rewrite <- hd_rev_eq_last.
    apply Z.ltb_ge; eauto.
    rewrite recode_rwnaf_length.
    lia.
    lia.
    lia.

    rewrite sbvToInt_sign_extend_16_64_equiv.
    erewrite bvSShr_Z_shiftr_equiv.
    symmetry.
    apply Z.div2_spec.
    lia.
    apply sbvToInt_intToBv_id.
    lia.
    (* windows are within range of word *)
    intuition idtac.
    eapply Z.lt_le_incl.
    eapply Z.le_lt_trans; [idtac | apply recode_rwnaf_bound_nth].
    apply (@Z.opp_le_mono (2 ^ Z.of_nat wsize)%Z).
    apply Z.pow_le_mono_r; lia.
    lia.
    lia.
    lia.
    eapply Z.lt_le_trans.
    apply recode_rwnaf_bound_nth; try lia.
    apply Z.pow_le_mono_r; lia.

    apply bvToNat_Z_to_nat_equiv.
    eapply Z.shiftr_nonneg.
    replace (List.nth (Nat.pred (S (S (S nw))))
   (recode_rwnaf wsize (S (S (S nw)))
      (BinInt.Z.of_nat (bvToNat 384%nat n))) 0)%Z
    with
    (List.last
   (recode_rwnaf wsize (S (S (S nw)))
      (BinInt.Z.of_nat (bvToNat 384%nat n))) 0)%Z.
    apply recode_rwnaf_last_nonneg.
    lia.
    lia.
    trivial.
    apply last_nth_equiv_gen.
    rewrite recode_rwnaf_length.
    trivial.
    lia.
    lia.
    rewrite sbvToInt_sign_extend_16_64_equiv.
    apply bvSShr_Z_shiftr_equiv.
    trivial.
    
    apply sbvToInt_intToBv_id.
    lia.
     intuition idtac.
    eapply Z.lt_le_incl.
    eapply Z.le_lt_trans; [idtac | apply recode_rwnaf_bound_nth].
    apply (@Z.opp_le_mono (2 ^ Z.of_nat wsize)%Z).
    apply Z.pow_le_mono_r; lia.
    lia.
    lia.
    lia.
    eapply Z.lt_le_trans.
    apply recode_rwnaf_bound_nth; try lia.
    apply Z.pow_le_mono_r; lia.

    lia.
    lia.

    rewrite hd_rev_eq_last.
    apply recode_rwnaf_last_nonneg.
    lia.
    lia.
    trivial.
    (* table is not huge *)
    erewrite <- Forall2_length; [ idtac | eapply preCompTable_equiv].
    rewrite tableSize_correct.
    unfold tableSize.
    rewrite shiftl_to_nat_eq.
    rewrite ZifyInst.of_nat_to_nat_eq.
    rewrite Z.shiftl_1_l.
    rewrite Z.max_r.
    apply Z.pow_lt_mono_r; lia.
    apply Z.pow_nonneg; lia.
    lia.
    apply nat_shiftl_gt_base; lia.

    apply bvToNat_lt_word.
    reflexivity.
   
    rewrite bvToNat_toZ_equiv.
    apply forall2_symm.
    eapply forall2_trans.
    apply mul_scalar_rwnaf_abstract_equiv.
    rewrite <- bvToNat_toZ_equiv.
    rewrite <- Z.shiftl_1_l.
    lia.
  
    intros.
    assert (b0 = c).
    eapply H1.
    subst.
    rewrite H0.
    rewrite sbvToInt_bvToInt_id.
    reflexivity.
    lia.
    eapply forall2_eq.
    reflexivity.

    rewrite skipn_1_eq_tl.
    eapply Forall2_tl.
    eapply Forall2_rev.
    rewrite bvToNat_toZ_equiv.
    eapply mul_scalar_rwnaf_abstract_equiv.
    rewrite <- Z.shiftl_1_l.
    rewrite <- bvToNat_toZ_equiv.
    lia.
 
    intros.  
    destruct wsize.
    lia.
    apply mul_body_equiv; trivial.
    lia.
    subst.
    eapply (@recode_rwnaf_bound_In (S n0) _ (S (S (S nw)))); try lia.
    eauto.
    apply in_rev.
    apply In_tl.
    eauto.
    rewrite rev_length.
    rewrite recode_rwnaf_length.
    lia.
    lia.
    lia.

    Unshelve.
    lia.

  Qed.


  Theorem point_mul_abstract_signedRegular_equiv : forall n p,
    (BinInt.Z.of_nat (bvToNat 384%nat n) <
 BinInt.Z.shiftl 1 (BinInt.Z.of_nat (S (S (S nw)) * wsize)))%Z->
    jac_eq
    (fromPoint
       (groupMul_signedRegular_table
          wsize (S (S (S nw))) p
          (bvToNat _ n)))
    (seqToProd
       (point_mul_abstract wsize nw (Nat.pred (Nat.pred (tableSize wsize))) (prodToSeq (fromPoint p))
          n)).

    intros.
    unfold point_mul_abstract.
    unfold groupMul_signedRegular_table, groupMul_signed_table.

    unfold groupMul_signedRegular, groupMul_signedRegularWindows.

    eapply jac_eq_symm.
    eapply jac_eq_trans.
    eapply conditional_subtract_if_even_jac_eq_ite.

    case_eq (Nat.even (bvToNat _ n)); intros.

    eapply jac_eq_symm.
    eapply point_add_jac_eq.
    eapply jac_eq_symm.
    eapply point_mul_abstract_signedRegular_cases.
    trivial.
    trivial.

    rewrite pre_comp_table_abstract_nth_0.
    apply jac_eq_refl_abstract.
    unfold point_opp, prodToSeq, seqToProd.
    simpl.
    destruct p. simpl. destruct x. destruct p. simpl.
    unfold nth_order. simpl.
    reflexivity.

    apply point_mul_abstract_signedRegular_cases; trivial.

  Qed.


  Definition affineOpp (x : affine_point) :=
    cons _ (nth_order x zero_lt_two) _ (cons _ (Fopp (nth_order x one_lt_two)) _ (@nil F)).

  Definition point_mul_base := point_mul_base Fsquare Fmul Fsub Fadd Fopp.
  Variable base_precomp_table : list (list affine_point).
  Definition numPrecompExponentGroups : nat := (Nat.pred wsize).
  Definition precompTableSize : nat := List.length base_precomp_table.
  Hypothesis precompTableSize_nz : precompTableSize <> 0%nat.
  Hypothesis base_precomp_table_entry_length : 
    forall ls, List.In ls base_precomp_table -> List.length ls = Nat.pow 2 numPrecompExponentGroups.
  Variable g : point.
  Definition affineToJac (a : affine_point) : Vec 3 F :=
    (append _ _ _ a (cons _ Fone 0 (@nil F))).
  Definition affine_default :=  List.hd (cons _ Fone _ (cons _ Fone _ (@nil F))) (List.hd List.nil base_precomp_table ) .
  Hypothesis base_precomp_table_correct : forall n1 n2,
    (n1 < precompTableSize)%nat ->
    (n2 < Nat.pow 2 numPrecompExponentGroups)%nat-> 
    jac_eq (seqToProd (affineToJac (List.nth n2 (List.nth n1 base_precomp_table List.nil) affine_default))) (fromPoint (groupMul ((2 * n2 + 1) * (Nat.pow 2 (n1 * numPrecompExponentGroups * wsize))) g)).

  Definition on_curve (p : affine_point ) : Prop :=
    let x := nth_order p zero_lt_two in
    let y := nth_order p one_lt_two in 
    Feq (y^2) (x^3 + a * x + b).

  Theorem affineOpp_on_curve : forall p,
    on_curve p -> 
    on_curve (affineOpp p).

    unfold on_curve, affineOpp in *.
    intros.
    unfold nth_order in *.
    simpl in *.
    replace (Fopp (nth p (Fin.FS Fin.F1)) ^ 2) with ( (nth p (Fin.FS Fin.F1)) ^ 2).
    trivial.
    nsatz.

  Qed.

  Definition affineOppIfNegative z p :=
     if (ZArith_dec.Z_lt_ge_dec z 0) then (affineOpp p) else p.

  Theorem affineOppIfNegative_on_curve : forall z p,
    on_curve p -> 
    on_curve (affineOppIfNegative z p).

    intros.
    unfold affineOppIfNegative.
    destruct (ZArith_dec.Z_lt_ge_dec z 0); trivial.
     eapply affineOpp_on_curve; eauto.

  Qed.

  Definition affinePointLookup (n m : nat) :=
    List.nth n (List.nth m base_precomp_table List.nil) affine_default.

  Theorem is_jacobian_on_curve : forall p,
    is_jacobian (seqToProd (affineToJac p)) -> 
    on_curve p.

    intros.
    unfold is_jacobian, affineToJac, on_curve in *.
    simpl in *.
    destruct (Vec_S_cons _ _ p).
    destruct H0.
    subst.
    destruct (Vec_S_cons _ _ x0).
    destruct H0.
    subst.
    unfold nth_order in *.
    simpl in *.
    unfold sawAt in *.
    simpl in *.
    unfold Feq in *.
    destruct (dec (1 = 0)).
    nsatz.
    rewrite H.
    nsatz.
  Qed.

  Theorem base_precomp_table_on_curve : 
    forall ls p, 
    List.In p ls -> 
    List.In ls base_precomp_table -> 
    on_curve p.

    intros.
    eapply is_jacobian_on_curve.
    destruct (In_nth ls p affine_default H).
    destruct H1.
    subst.
    destruct (In_nth base_precomp_table ls List.nil H0).
    destruct H2.
    subst.  
    eapply jac_eq_is_jacobian; [idtac | apply jac_eq_symm; apply base_precomp_table_correct].
    eapply fromPoint_is_jacobian.
    eauto.
    erewrite base_precomp_table_entry_length in H1.
    lia.
    eauto.

  Qed.

  Theorem affine_default_on_curve : on_curve affine_default.
    unfold affine_default.
    eapply base_precomp_table_on_curve.
    repeat rewrite <- nth_0_hd_equiv.
    eapply nth_In.
    rewrite base_precomp_table_entry_length.
    assert (Nat.pow 2 numPrecompExponentGroups <> 0)%nat.
    apply NPeano.Nat.pow_nonzero.
    lia.
    lia.
    eapply nth_In.
    unfold precompTableSize in *.
    lia.
    eapply nth_In.
    unfold precompTableSize in *.
    lia.
  Qed.

  Theorem affinePointLookup_on_curve : forall n m,
    on_curve (affinePointLookup n m).
 
    intros.
    unfold affinePointLookup.
    destruct (dec (n < (List.length (List.nth m base_precomp_table []) ))).
    eapply Forall_nth; trivial.
    eapply List.Forall_forall.
    intros.
    destruct (dec (m < List.length base_precomp_table)).
    eapply base_precomp_table_on_curve.
    eauto.
    apply nth_In.
    lia.
    rewrite nth_overflow in H.
    simpl in *.
    intuition idtac.
    lia.
    rewrite nth_overflow.
    apply affine_default_on_curve.
    lia.

  Qed.

  Theorem affineIsJacobian : forall affinePt,
    on_curve affinePt -> 
    is_jacobian (seqToProd (affineToJac affinePt)).

    intros.
    unfold affineToJac, is_jacobian, on_curve in *.
    simpl.
    replace (nth_order (append 2 1 felem affinePt (cons F 1 0 (nil F))) two_lt_three)  with 1.
    destruct (dec (Feq 1 0)).
    trivial.
    replace (b * (1 ^ 3) ^ 2) with b.
    replace (a * nth_order (append 2 1 felem affinePt (cons F 1 0 (nil F))) zero_lt_three * (1 ^ 2) ^ 2) with (a * nth_order (append 2 1 felem affinePt (cons F 1 0 (nil F))) zero_lt_three).
    erewrite (@nth_order_append_l_eq _ _ 1%nat _ 2%nat _ _ _ one_lt_two ).  
    repeat erewrite (@nth_order_append_l_eq _ _ 1%nat _ 2%nat _ _ _ zero_lt_two ).
    apply H.
    nsatz.
    nsatz.
    symmetry.
    erewrite (@nth_order_append_eq felem _ 1%nat (cons F 1 0 (nil F)) 2%nat affinePt 0%nat two_lt_three ).
    reflexivity.

    Unshelve. 
    lia.
  Qed.

  Definition pExpMultiple (n : nat) (x : Z) : point := 
    let absPt := affinePointLookup (Z.to_nat (Z.div2 (Z.abs x))) n in
    let affinePt :=  affineOppIfNegative x absPt in
    toPoint (seqToProd (affineToJac affinePt)) (affineIsJacobian (affineOppIfNegative_on_curve _ (affinePointLookup_on_curve _ _ ))).

  Theorem affineOpp_toPoint_eq :  forall p,
    jac_eq
    (seqToProd
       (affineToJac
          (affineOpp p))) 
     (seqToProd (point_opp (affineToJac p))).

    intros.
    unfold point_opp, EC_P384_Abstract.point_opp.
    unfold affineOpp, affineToJac.
    unfold affine_point in *.
    unfold nth_order in *.
    simpl.
    repeat rewrite sawAt_nth_equiv; try lia.
    unfold nth_order.
    simpl.
    repeat rewrite sawAt_nth_equiv; try lia.
    unfold nth_order.
    simpl.
    destructVec.
    simpl.
    destruct (dec (Feq 1 0)).
    trivial.
    intuition idtac.
    reflexivity.
    reflexivity.

  Qed.

  Theorem Z_odd_abs_eq : forall z,
    Z.odd (Z.abs z) = Z.odd z.

    intros.
    destruct z; simpl in *;
    reflexivity.

  Qed.
  
  Theorem OddWindow_precomp_abs_le : forall w,
    OddWindow wsize w -> 
    Z.to_nat (Z.div2 (Z.abs w)) < Nat.pow 2 numPrecompExponentGroups.

    unfold OddWindow, GroupMulWNAF.OddWindow in *.
    intuition idtac.
    eapply PeanoNat.Nat.lt_le_trans.
    eapply Znat.Z2Nat.inj_lt.
    eapply Z.div2_nonneg.
    lia.
    assert (0 <= Z.pow 2 (Z.of_nat numPrecompExponentGroups))%Z.
    lia.
    eauto.
    eapply Z.lt_le_trans.
    eapply Zdigits.Zdiv2_two_power_nat.
    lia.
    assert (Z.abs w < Zpower.two_power_nat (S (Nat.pred wsize)))%Z.
    rewrite PeanoNat.Nat.succ_pred_pos.
    rewrite Z.shiftl_mul_pow2 in *.
    eapply Z.lt_le_trans.
    eauto.
    rewrite Z.mul_1_l.
    rewrite Zpower.two_power_nat_equiv.
    reflexivity.
    lia.
    lia.
    eauto.
    rewrite Zpower.two_power_nat_equiv.
    reflexivity.

    rewrite Znat.Z2Nat.inj_pow.
    rewrite Znat.Nat2Z.id.
    reflexivity.
    lia.
    lia.

  Qed.

  Theorem wsize_precomp_correct : 
    wsize = S numPrecompExponentGroups.

    unfold numPrecompExponentGroups.
    rewrite PeanoNat.Nat.succ_pred_pos.
    reflexivity.
    lia.
  Qed.

  Theorem OddWindow_precomp_le : forall w,
    (0 <= w)%Z ->
    OddWindow wsize w -> 
    Z.to_nat (Z.div2 w) < Nat.pow 2 numPrecompExponentGroups.

    unfold OddWindow, GroupMulWNAF.OddWindow in *.
    intros.
    destruct H0.
    eapply PeanoNat.Nat.lt_le_trans.
    eapply Znat.Z2Nat.inj_lt.
    eapply Z.div2_nonneg.
    lia.
    assert (0 <= Z.pow 2 (Z.of_nat numPrecompExponentGroups))%Z.
    lia.
    eauto.
    eapply Z.lt_le_trans.
    eapply Zdigits.Zdiv2_two_power_nat.
    lia.
    rewrite <- wsize_precomp_correct.
    rewrite Z.shiftl_mul_pow2 in *.
    eapply Z.lt_le_trans.
    rewrite Z.abs_eq in *.
    eauto.
    lia.
    rewrite Z.mul_1_l.
    rewrite Zpower.two_power_nat_equiv.
    reflexivity.
    lia.
    rewrite Zpower.two_power_nat_equiv.
    reflexivity.
    rewrite Znat.Z2Nat.inj_pow.
    rewrite Znat.Nat2Z.id.
    reflexivity.
    lia.
    lia.

  Qed.

  Theorem pExpMultiple_correct : forall n w,
        (n < precompTableSize)%nat -> 
        OddWindow wsize w ->
        pExpMultiple n w == groupMul_doubleAdd_signed (Z.shiftl w  (Z.of_nat (numPrecompExponentGroups * wsize * n))) g.

    intros.
    unfold pExpMultiple.
    unfold groupMul_doubleAdd_signed.
    destruct (ZArith_dec.Z_lt_ge_dec w 0).
    case_eq (Z.shiftl w (Z.of_nat (numPrecompExponentGroups * wsize * n))); intros.
    apply Z.shiftl_eq_0_iff in H1.
    subst. lia.
    lia.
    assert (0 <= w)%Z.
    eapply Z.shiftl_nonneg.
    rewrite H1.
    lia.
    lia.

    eapply jac_eq_jacobian_eq.
    rewrite <- fromPoint_toPoint_id.
    unfold affineOppIfNegative.
    destruct (ZArith_dec.Z_lt_ge_dec w 0).
    assert ( jac_eq
      (seqToProd (affineToJac (affineOpp (affinePointLookup (Z.to_nat (Z.div2 (Z.abs w))) n))))
      (seqToProd (point_opp (affineToJac (affinePointLookup (Z.to_nat (Z.div2 (Z.abs w))) n))))
    ).
   
    eapply affineOpp_toPoint_eq.
    eapply jac_eq_trans; eauto.
    eapply jac_eq_symm.
    eapply jac_eq_trans.
    eapply point_opp_equiv.
    eapply point_opp_jac_eq_proper.
    clear H2.
    eapply jac_eq_symm.
    eapply jac_eq_trans.
    eapply base_precomp_table_correct.
    trivial.
    eapply OddWindow_precomp_abs_le; eauto.
    
    eapply jac_eq_symm.
    assert ((groupMul_doubleAdd_pos p g)
    ==
    groupMul (Pos.to_nat p) g
    ).
    eapply groupMul_doubleAdd_pos_equiv.

    rewrite seqToProd_inv.
    eapply jac_eq_trans.
    eapply jacobian_eq_jac_eq.
    eapply H2.
    clear H2.
    rewrite Z.shiftl_mul_pow2 in H1.
    replace (2 * Z.to_nat (Z.div2 (Z.abs w)) + 1)%nat  with (Z.to_nat (Z.abs w)).
    rewrite <- Znat.Z2Nat.inj_pos.
    replace (Z.pos p) with (Z.abs (Z.neg p)).
    rewrite <- H1.
    unfold groupMul.
    replace (BinInt.Z.to_nat (Z.abs (w * 2 ^ (Z.of_nat (numPrecompExponentGroups * wsize * n))))) with 
      (Z.to_nat (Z.abs w) * Nat.pow 2 (n * numPrecompExponentGroups * wsize))%nat.
    eapply jac_eq_refl.
    rewrite Z.abs_mul.
    rewrite Znat.Z2Nat.inj_mul.
    f_equal.
    rewrite Z.abs_eq.
    rewrite Znat.Z2Nat.inj_pow.
    rewrite Znat.Nat2Z.id.
    f_equal.
    rewrite (NPeano.Nat.mul_comm (numPrecompExponentGroups * wsize)%nat). 
    rewrite NPeano.Nat.mul_assoc.
    reflexivity.
    lia.
    lia.
    lia.
    lia.
    lia.

    reflexivity.
    unfold OddWindow, GroupMulWNAF.OddWindow in *.
    intuition idtac; subst.
    replace (2 * Z.to_nat (Z.div2 (Z.abs w)) + 1)%nat with (Z.to_nat (2 * Z.div2 (Z.abs w) + (if BinInt.Z.odd (Z.abs w) then 1 else 0))).
    f_equal.
    apply Zeven.Zdiv2_odd_eqn.
    rewrite Z_odd_abs_eq.
    rewrite H4.
    rewrite Znat.Z2Nat.inj_add.
    f_equal.
    rewrite Znat.Z2Nat.inj_mul.
    reflexivity.
    lia.
    apply Z.div2_nonneg.
    lia.
    apply Z.mul_nonneg_nonneg.
    lia.
    apply Z.div2_nonneg.
    lia.
    lia.

    lia.

    rewrite Z.abs_eq; try lia.
    case_eq (Z.shiftl w (Z.of_nat (numPrecompExponentGroups * wsize * n))); intros.
    assert (w = 0)%Z.
    apply Z.shiftl_eq_0_iff in H1.
    subst. lia.
    lia.
    subst.
    unfold OddWindow, GroupMulWNAF.OddWindow in *.
    intuition idtac.
    simpl in *.
    discriminate.

    rewrite Z.shiftl_mul_pow2 in H1.
    eapply jac_eq_jacobian_eq.
    rewrite <- fromPoint_toPoint_id.  
    unfold affineOppIfNegative.
    destruct (ZArith_dec.Z_lt_ge_dec w 0); try lia.
    eapply jac_eq_trans.
    eapply base_precomp_table_correct.
    trivial.
    eapply OddWindow_precomp_le; eauto.
    lia.
    rewrite Z.abs_eq.
    trivial.
    lia.
    eapply jac_eq_symm.
    assert ((groupMul_doubleAdd_pos p g)
    ==
    groupMul (Pos.to_nat p) g
    ).
    eapply groupMul_doubleAdd_pos_equiv.
  
    eapply jac_eq_trans.
    eapply jacobian_eq_jac_eq.
    eapply H2.
    clear H2.
    rewrite Z.abs_eq; try lia.
    replace (2 * Z.to_nat (Z.div2 w) + 1)%nat  with (Z.to_nat w).
    rewrite <- Znat.Z2Nat.inj_pos.
    rewrite <- H1.
    unfold groupMul.
    replace (BinInt.Z.to_nat (w * 2 ^ (Z.of_nat (numPrecompExponentGroups * wsize * n)))) with 
      (Z.to_nat w * Nat.pow 2 (n * numPrecompExponentGroups * wsize))%nat.
    eapply jac_eq_refl.
    rewrite Znat.Z2Nat.inj_mul.
    f_equal.
    rewrite Znat.Z2Nat.inj_pow.
    rewrite Znat.Nat2Z.id.
    f_equal.
    rewrite (NPeano.Nat.mul_comm (numPrecompExponentGroups * wsize)%nat). 
    rewrite NPeano.Nat.mul_assoc.
    reflexivity.
    lia.
    lia.
    lia.
    lia.

    unfold OddWindow, GroupMulWNAF.OddWindow in *.
    intuition idtac; subst.
    replace (2 * Z.to_nat (Z.div2 w) + 1)%nat with (Z.to_nat (2 * Z.div2 w+ (if BinInt.Z.odd w then 1 else 0))).
    f_equal.
    apply Zeven.Zdiv2_odd_eqn.
    rewrite H4.
    rewrite Znat.Z2Nat.inj_add.
    f_equal.
    rewrite Znat.Z2Nat.inj_mul.
    reflexivity.
    lia.
    apply Z.div2_nonneg.
    lia.
    apply Z.mul_nonneg_nonneg.
    lia.
    apply Z.div2_nonneg.
    lia.
    lia.
    lia.

    (* contradiction *)
    assert (w < 0)%Z.
    eapply Z.shiftl_neg.
    rewrite H1.
    lia.
    lia.
  Qed.
 
  Definition groupedMul_scalar_precomp numPrecompExponentGroups wsize nw d s :=
    match (groupedMul_precomp wsize nw g numPrecompExponentGroups pExpMultiple d (recode_rwnaf wsize nw (Z.of_nat s))) with
    | Some x => 
      if (Nat.even s) then Some (Jacobian.add x (Jacobian.opp g)) else Some x
    | None => None
    end.

  Theorem zero_point_jac_eq : 
    jac_eq (fromPoint zero_point)
     (seqToProd (replicate 3 (Vec 6 (bitvector 64)) (replicate 6 (bitvector 64) (intToBv 64 0)))).

    unfold zero_point, zero_point_h.
    simpl.
    destruct (dec (Feq 0 0)). trivial.
    exfalso.
    intuition idtac.
    eapply n. reflexivity.
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
    rewrite H4.
    rewrite H.
    econstructor.
    econstructor.
    exists (List.map (fun x => x ++ [wm_Double d]) x1).
    intuition idtac.
    rewrite map_length.
    rewrite List.map_map.
    erewrite (combineOpt_map_map _ (fun x => Some (x ++ [wm_Double d])) );[
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

  Theorem groupDouble_n_fold_left_double_abstract_equiv
     : forall (ws : nat) (A: Type)(ls : list A) (a1 : point) (a2 : seq 3 F),
       Datatypes.length ls = ws ->
       jac_eq (fromPoint a1) (seqToProd a2) ->
       jac_eq (fromPoint (groupDouble_n ws a1))
         (seqToProd
            (List.fold_left
               (fun (x : seq 3 (seq 6 (seq 64 Bool))) (_ : A) =>
                EC_P384_Abstract.point_double Fsquare Fmul Fsub Fadd x) ls a2)).

      induction ws; destruct ls; intros; simpl in *; try lia.
      trivial.
      eapply jac_eq_trans; [idtac | eapply IHws].
      apply jacobian_eq_jac_eq.
      eapply groupDouble_n_double_comm_jac.
      lia.
      assert (exists a2', (seqToProd a2) = (fromPoint a2')).
      eapply jac_eq_point_ex; eauto.
      destruct H1. subst.
      replace a2 with (prodToSeq (fromPoint x)).
      rewrite <- double_eq_minus_3.
      rewrite seqToProd_inv.
      apply jacobian_eq_jac_eq.
      transitivity (Jacobian.double x).
      apply Jacobian.Proper_double.
      eapply jac_eq_jacobian_eq.
      eapply jac_eq_trans; eauto.
      eapply jac_eq_refl_abstract.
      trivial.

      eapply Jacobian.double_minus_3_eq_double.
      rewrite <- H1.
      apply prodToSeq_inv.
    
  Qed.

  Theorem affineToJac_cons_eq : forall z,
      affineToJac z =
      cons (seq 6 (seq 64 bool)) (nth_order z zero_lt_two) 2
        (cons (seq 6 (seq 64 bool)) (nth_order z one_lt_two) 1
           (cons (seq 6 (seq 64 bool)) 1 0 (nil (seq 6 (seq 64 bool))))).

    intros.
    unfold affineToJac. 
    destruct (Vec_S_cons _ _ z). destruct H.
    destruct (Vec_S_cons _ _ x0). destruct H0.
    subst.
    rewrite (Vec_0_nil _ x2).
    rewrite SAWCorePrelude_proofs.append_cons.
    simpl.
    rewrite SAWCorePrelude_proofs.append_cons.
    simpl.
    rewrite append_nil_eq.
    f_equal.

  Qed.


  Theorem add_base_abstract_jac_add_equiv_h:  forall n p (rwnaf : list (t bool 16)),
    n < List.length rwnaf -> 
    Nat.div n numPrecompExponentGroups < Datatypes.length base_precomp_table -> 
    List.Forall (fun x => OddWindow wsize (sbvToInt _ x)) rwnaf -> 
    jac_eq 
      (seqToProd (add_base_abstract Fsquare Fmul Fsub Fadd Fopp base_precomp_table 1 numPrecompExponentGroups rwnaf (prodToSeq (fromPoint p)) n))
      (fromPoint (Jacobian.add p (pExpMultiple (Nat.div n numPrecompExponentGroups) (sbvToInt _ (List.nth n rwnaf (vecRepeat 0%bool 16)))))).

    intros.
    unfold add_base_abstract.
    remember (select_point_affine_abstract
                       (sign_extend_16_64
                          (bvSShr 15
                             (bvAdd 16
                                (shiftR 16 bool 0%bool
                                   (List.nth n rwnaf (vecRepeat 0%bool 16)) 15)
                                (bvXor 16 (List.nth n rwnaf (vecRepeat 0%bool 16))
                                   (bvSShr 15 (List.nth n rwnaf (vecRepeat 0%bool 16)) 15))) 1))
                       (List.nth (PeanoNat.Nat.div n numPrecompExponentGroups) base_precomp_table [])) as z.

    rewrite select_point_affine_abstract_nth_equiv in Heqz.
    remember (List.nth n rwnaf (vecRepeat 0%bool 16)) as m.
    rewrite (@bvToNat_Z_to_nat_equiv _ _ (sbvToInt _ (sign_extend_16_64
               (bvSShr 15 (bvAdd 16 (shiftR 16 bool 0%bool m 15) (bvXor 16 m (bvSShr 15 m 15)))
                  1)))) in Heqz.
    rewrite sbvToInt_sign_extend_16_64_equiv in Heqz.
    rewrite (@bvSShr_Z_shiftr_equiv _ _ (Z.abs (sbvToInt _ m)) _ 1%Z) in Heqz.
    rewrite felem_cmovznz_equiv.
    eapply jac_eq_symm.
    eapply point_add_mixed_eq.
    erewrite nth_order_S_cons.
    erewrite nth_order_S_cons.
    erewrite nth_order_0_cons.
    trivial.

    rewrite seqToProd_inv.
    eapply jac_eq_refl.

    case_eq (bvEq 64 (point_id_to_limb (bvShr 16 m 15)) (intToBv 64 0)); intros.
    replace (cons (seq 6 (seq 64 bool)) (nth_order z zero_lt_two) 2
           (cons (seq 6 (seq 64 bool)) (nth_order z one_lt_two) 1
              (cons (seq 6 (seq 64 bool)) 1 0 (nil (seq 6 (seq 64 bool))))))
      with
      (affineToJac z).
    subst.
    unfold pExpMultiple.
    rewrite Z.abs_eq.
    destruct (ZArith_dec.Z_lt_ge_dec
                  (sbvToInt 16 (List.nth n rwnaf (vecRepeat 0%bool 16))) 0).
    exfalso.
    rewrite bvShr_shiftR_equiv in *.
    rewrite shiftR_all_neg in H2.
    replace (point_id_to_limb (intToBv 16 1)) with (intToBv 64 1) in *.
    apply bvEq_eq in H2.
    assert (1 = 0)%Z.
    eapply intToBv_eq_pos; eauto.
    lia.
    lia.
    discriminate.
    reflexivity.
    lia.
    trivial.

    rewrite <- fromPoint_toPoint_id.
    rewrite Z.div2_spec.
    unfold affineOppIfNegative, affinePointLookup.
    destruct (ZArith_dec.Z_lt_ge_dec (sbvToInt 16 (List.nth n rwnaf (vecRepeat 0%bool 16))) 0); try lia.
    rewrite (nth_indep _ affine_default (cons F 0 1 (cons F 0 0 (nil F)))).
    eapply jac_eq_refl.
    specialize (base_precomp_table_entry_length (List.nth (Nat.div n numPrecompExponentGroups) base_precomp_table [])); intros.

    match goal with
    | [|- _ < ?a ] => replace a with (Nat.pow 2 numPrecompExponentGroups)
    end.

    assert (OddWindow wsize (sbvToInt 16 (List.nth n rwnaf (vecRepeat 0%bool 16)))).
    eapply List.Forall_forall in H1.
    eapply H1.
    eapply nth_In.
    lia.
    unfold OddWindow, GroupMulWNAF.OddWindow in H3.
    intuition idtac.
    rewrite Z.abs_eq in H7; try lia.
    repeat rewrite <- Z.div2_spec in *.
    replace (BinInt.Z.shiftl 1 (BinInt.Z.of_nat wsize)) with (2 * (BinInt.Z.shiftl 1 (BinInt.Z.of_nat numPrecompExponentGroups)))%Z in H7.
    eapply NPeano.Nat.lt_le_trans.
    eapply (Znat.Z2Nat.inj_lt _ (BinInt.Z.shiftl 1 (BinInt.Z.of_nat numPrecompExponentGroups))).
    eapply Z.div2_nonneg.
    lia.
    eapply Z.shiftl_nonneg.
    lia.
    eapply div2_lt.
    eauto.
    rewrite Z.shiftl_1_l.
    rewrite Znat.Z2Nat.inj_pow.
    rewrite Znat.Nat2Z.id.
    reflexivity.
    lia.
    lia.
    unfold numPrecompExponentGroups.
    rewrite Z.shiftl_1_l.
    rewrite <- (@Z.pow_add_r 2 1)%Z.
    replace (1 + BinInt.Z.of_nat (Nat.pred wsize))%Z with (BinInt.Z.of_nat wsize).
    rewrite Z.shiftl_1_l.
    reflexivity.
    lia.
    lia.
    lia.
    symmetry.
    apply base_precomp_table_entry_length.
    eapply nth_In.
    lia.

    rewrite bvShr_shiftR_equiv in *.
    apply bvEq_eq in H2.
    destruct (dec (0 <= sbvToInt 16 (List.nth n rwnaf (vecRepeat 0%bool 16))))%Z; trivial.
    exfalso.
    rewrite shiftR_all_neg in H2.
    replace (point_id_to_limb (intToBv 16 1)) with (intToBv 64 1) in *.
    assert (1 = 0)%Z.
    eapply intToBv_eq_pos; eauto.
    lia.
    lia.
    discriminate.
    reflexivity.
    lia.
    lia.

    eapply affineToJac_cons_eq.

    replace  (seqToProd
     (cons (seq 6 (seq 64 bool)) (nth_order z zero_lt_two) 2
        (cons (seq 6 (seq 64 bool)) (Fopp (nth_order z one_lt_two)) 1
           (cons (seq 6 (seq 64 bool)) 1 0 (nil (seq 6 (seq 64 bool)))))))
      with
    (seqToProd (affineToJac (affineOpp z))).
    subst.
    unfold pExpMultiple.
    rewrite <- fromPoint_toPoint_id.
    unfold affineOppIfNegative, affinePointLookup.
    destruct (ZArith_dec.Z_lt_ge_dec (sbvToInt 16 (List.nth n rwnaf (vecRepeat 0%bool 16)))).
    rewrite Z.div2_spec.
    rewrite (nth_indep _ affine_default (cons F 0 1 (cons F 0 0 (nil F)))).
    eapply jac_eq_refl.
    match goal with
    | [|- _ < ?a ] => replace a with (Nat.pow 2 numPrecompExponentGroups)
    end.
    assert (OddWindow wsize (sbvToInt 16 (List.nth n rwnaf (vecRepeat 0%bool 16)))).
    eapply List.Forall_forall in H1.
    eapply H1.
    eapply nth_In.
    lia.
    unfold OddWindow, GroupMulWNAF.OddWindow in H3.
    intuition idtac.
    repeat rewrite <- Z.div2_spec in *.
    replace (BinInt.Z.shiftl 1 (BinInt.Z.of_nat wsize)) with (2 * (BinInt.Z.shiftl 1 (BinInt.Z.of_nat numPrecompExponentGroups)))%Z in H7.
    eapply NPeano.Nat.lt_le_trans.
    eapply (Znat.Z2Nat.inj_lt _ (BinInt.Z.shiftl 1 (BinInt.Z.of_nat numPrecompExponentGroups))).
    eapply Z.div2_nonneg.
    lia.
    eapply Z.shiftl_nonneg.
    lia.
    eapply div2_lt.
    eauto.
    rewrite Z.shiftl_1_l.
    rewrite Znat.Z2Nat.inj_pow.
    rewrite Znat.Nat2Z.id.
    reflexivity.
    lia.
    lia.
    unfold numPrecompExponentGroups.
    rewrite Z.shiftl_1_l.
    rewrite <- (@Z.pow_add_r 2 1)%Z.
    replace (1 + BinInt.Z.of_nat (Nat.pred wsize))%Z with (BinInt.Z.of_nat wsize).
    rewrite Z.shiftl_1_l.
    reflexivity.
    lia.
    lia.
    lia.
    symmetry.
    apply base_precomp_table_entry_length.
    eapply nth_In.
    lia.

    (* contradiction *)
    exfalso.
    rewrite bvShr_shiftR_equiv in *.
    rewrite shiftR_all_nonneg in H2.
    rewrite rep_false_eq_int_bv in *.
    replace (point_id_to_limb (intToBv 16 0)) with (intToBv 64 0) in *.
    apply bvEq_neq in H2.
    intuition idtac.
    reflexivity.
    lia.
    lia.

    unfold affineToJac, affineOpp.
    simpl.
    f_equal.

    reflexivity.
    eapply ct_abs_equiv.
    subst.
    destruct (dec (n < (List.length rwnaf))%nat).
    eapply Forall_nth.
    eapply List.Forall_impl; eauto.
    intros.
    unfold OddWindow, GroupMulWNAF.OddWindow in *.
    intuition idtac.
    eapply Z.abs_lt in H6.
    eapply Z.le_lt_trans; [idtac | eapply H6].
    rewrite Z.shiftl_mul_pow2.
    apply (Z.opp_le_mono (1 * 2 ^ BinInt.Z.of_nat wsize)).
    rewrite Z.mul_1_l.
    eapply Z.pow_le_mono_r.
    lia.
    lia.
    lia.
    lia.
    rewrite nth_overflow.
    replace (sbvToInt 16 (vecRepeat 0%bool 16)) with 0%Z.
    lia.
    reflexivity.
    lia.

    reflexivity.
    rewrite <- (sbvToInt_bvToInt_id (bvAdd 16 (shiftR 16 bool 0%bool m 15) (bvXor 16 m (bvSShr 15 m 15)))).
    erewrite ct_abs_equiv; try reflexivity.
    rewrite sbvToInt_sign_extend_16_64_equiv.
    erewrite bvSShr_Z_shiftr_equiv; try reflexivity.
    rewrite sbvToInt_intToBv_id.
    eapply Z.shiftr_nonneg.
    lia.
    lia.
    intuition idtac; try lia.
    destruct (dec (n < (List.length rwnaf))%nat).
    subst.
    eapply Forall_nth.
    eapply List.Forall_impl; eauto.
    intros.
    unfold OddWindow, GroupMulWNAF.OddWindow in *; simpl in *.
    intuition idtac.
    eapply Z.lt_le_trans.
    eapply H6.
    rewrite Z.shiftl_1_l.
    rewrite Z.pow_pos_fold.
    eapply Z.pow_le_mono_r.
    lia.
    lia.
    lia.
    subst.
    rewrite nth_overflow.
    replace (sbvToInt 16 (vecRepeat 0%bool 16)) with 0%Z.
    lia.
    reflexivity.
    lia.
    subst.
    destruct (dec (n < (List.length rwnaf))%nat).
    eapply Forall_nth.
    eapply List.Forall_impl; eauto.
    intros.
    unfold OddWindow, GroupMulWNAF.OddWindow in *; simpl in *.
    intuition idtac.
    apply Z.abs_lt in H6.
    eapply Z.le_lt_trans; [idtac | apply H6].
    rewrite Z.shiftl_1_l.
    replace (-32768)%Z with (- (2 ^ 15))%Z.
    eapply (Z.opp_le_mono (2 ^ BinInt.Z.of_nat wsize)%Z) ; intros.
    eapply Z.pow_le_mono_r.
    lia.
    lia.
    reflexivity.
    lia.
    rewrite nth_overflow.
    replace (sbvToInt 16 (vecRepeat 0%bool 16)) with 0%Z.
    lia.
    reflexivity.
    lia.
    lia.
    reflexivity.

    destruct (dec ((PeanoNat.Nat.div n numPrecompExponentGroups) < (List.length base_precomp_table))).
    rewrite base_precomp_table_entry_length.
    rewrite Znat.Nat2Z.inj_pow.
    eapply Z.pow_lt_mono_r.
    lia.
    lia.
    unfold numPrecompExponentGroups.
    lia.
    eapply nth_In; eauto.
    rewrite nth_overflow.
    simpl.
    lia.
    lia.

    apply bvToNat_lt_word.

    Unshelve.
    lia.
    lia.
  Qed.

  Theorem add_base_abstract_jac_add_equiv:  forall n n' p1 p2 (rwnaf : list (t bool 16)),
    List.Forall (fun x => OddWindow wsize (sbvToInt _ x)) rwnaf -> 
    Nat.gcd n numPrecompExponentGroups = numPrecompExponentGroups -> 
    (Nat.div n numPrecompExponentGroups = Nat.div n' numPrecompExponentGroups) -> 
    jac_eq (fromPoint p2) (seqToProd p1) -> 
    (n' < List.length rwnaf <= numPrecompExponentGroups * precompTableSize)%nat -> 
    jac_eq 
      (seqToProd (add_base_abstract Fsquare Fmul Fsub Fadd Fopp base_precomp_table 1 numPrecompExponentGroups rwnaf p1 n'))
      (fromPoint (Jacobian.add p2 (groupMul_doubleAdd_signed
        ((sbvToInt _ (List.nth n' rwnaf (vecRepeat 0%bool 16))) * (Z.pow 2 (Z.of_nat (wsize * n)))) g))).

    intros.
    
    assert (is_jacobian (seqToProd p1)).
    eapply jac_eq_is_jacobian; eauto. 
    eapply fromPoint_is_jacobian.

    eapply jac_eq_symm.
    eapply jac_eq_trans.
    eapply jacobian_eq_jac_eq.
    eapply Jacobian.Proper_add.
    eapply jac_eq_jacobian_eq.
    assert (jac_eq (fromPoint p2) (fromPoint (toPoint (seqToProd p1) H4))).   
    rewrite <- fromPoint_toPoint_id.
    eauto.
    eauto.
    reflexivity.
    eapply jac_eq_symm.
    replace p1 with (prodToSeq (fromPoint (toPoint (seqToProd p1) H4))) at 1.
    eapply jac_eq_trans.
    eapply add_base_abstract_jac_add_equiv_h.
    lia.
    eapply NPeano.Nat.div_lt_upper_bound.
    lia.
    unfold precompTableSize in *.
    lia.

    eauto.
    eapply jacobian_eq_jac_eq.
    eapply Jacobian.Proper_add.
    reflexivity.
    rewrite pExpMultiple_correct.
    rewrite <- H1.
    rewrite Z.shiftl_mul_pow2.
    replace (numPrecompExponentGroups * wsize * Nat.div n numPrecompExponentGroups)%nat with (wsize * n)%nat.
    reflexivity.
    rewrite (NPeano.Nat.mul_comm numPrecompExponentGroups).
    rewrite <- NPeano.Nat.mul_assoc.
    f_equal.
    rewrite PeanoNat.Nat.gcd_comm in H0.
    rewrite <- H0 at 2.
    rewrite <- PeanoNat.Nat.gcd_div_swap.
    rewrite H0.
    rewrite PeanoNat.Nat.div_same.
    lia.
    unfold numPrecompExponentGroups.
    lia.  
    lia.
    eapply NPeano.Nat.div_lt_upper_bound.
    unfold numPrecompExponentGroups; lia.
    lia.
    eapply Forall_nth.
    eauto.
    lia.
    rewrite <- fromPoint_toPoint_id.
    apply prodToSeq_inv.
  Qed.
  
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
    rewrite NPeano.Nat.add_0_r.
    econstructor; intuition idtac.
    edestruct IHls; eauto.
    intuition idtac; subst.
    exists x0.
    intuition idtac.
    f_equal.
    lia.

  Qed.

  Theorem double_add_base_abstract_equiv : forall ls  rwnaf1 rwnaf2 x0 x n p1 p2,
    List.Forall (fun x => OddWindow wsize (sbvToInt _ x)) rwnaf2 -> 
    List.Forall (fun x => Nat.gcd x numPrecompExponentGroups = numPrecompExponentGroups) (List.map (fun x => x - n)%nat ls)  -> 
    List.Forall (fun x => x < Datatypes.length rwnaf2) ls -> 
    rwnaf1 = List.map (fun x => sbvToInt _ x) rwnaf2 -> 
    jac_eq (fromPoint p1) (seqToProd p2) ->
    multiSelect (signedWindowsToProg rwnaf1 0) ls = Some x0 ->
    decrExpLs n x0 = Some x -> 
    List.Forall2 (fun x y => Nat.div x numPrecompExponentGroups = Nat.div y numPrecompExponentGroups) ls (List.map (fun x => x - n)%nat ls) ->
    Datatypes.length rwnaf2 <= numPrecompExponentGroups * precompTableSize ->
    jac_eq
      (fromPoint
         (groupMul_signedWindows_prog' wsize g p1 (x ++ [wm_Double 1])))
        (seqToProd
       (List.fold_left
          (add_base_abstract Fsquare Fmul Fsub Fadd Fopp base_precomp_table 1 numPrecompExponentGroups
             rwnaf2)
          (List.rev ls)
          (List.fold_left
              (fun (x0 : seq 3 (seq 6 (seq 64 bool))) (_ : nat) =>
               EC_P384_Abstract.point_double Fsquare Fmul Fsub Fadd x0)
              (forNats wsize) p2))).

    induction ls; intros; simpl in *.
    inversion H0; clear H0; subst.
    simpl in *.
    rewrite groupMul_signedWindows_prog'_app_equiv.
    unfold multiSelect in *.
    simpl in *.
    inversion H4; clear H4; subst.
    simpl in *.
    inversion H5; clear H5; subst.
    simpl in *.
    repeat rewrite <- plus_n_O.
    eapply groupDouble_n_fold_left_double_abstract_equiv.
    apply forNats_length.
    trivial.

    inversion H6; clear H6; subst.
    inversion H0; clear H0; subst.
    simpl in *.
    rewrite multiSelect_cons in *.  
    case_eq (nth_error (signedWindowsToProg (List.map (fun x : bitvector 16 => sbvToInt 16 x) rwnaf2) 0) a0 ); intros;
    rewrite H0 in H4.
    case_eq (multiSelect (signedWindowsToProg (List.map (fun x : bitvector 16 => sbvToInt 16 x) rwnaf2) 0) ls); intros;
    rewrite H2 in H4.
    inversion H4; clear H4; subst.
    simpl.
    rewrite fold_left_app.
    simpl.
 
    assert (exists x, nth_error (List.map (fun x : bitvector 16 => sbvToInt 16 x) rwnaf2) a0 = Some x /\ w = wm_Add a0 x).
    eapply nth_error_signedWindowsToProg_Some_add in H0.
    destruct H0.
    intuition idtac; subst.
    simpl.
    econstructor; intuition idtac; eauto.

    destruct H4.
    destruct H4.
    subst.
    simpl in *.
    destruct (Compare_dec.le_dec n a0).
    case_eq (decrExpLs n l); intros;
    rewrite H6 in H5.
    inversion H5; clear H5; subst.
    simpl in *.
    eapply jac_eq_trans.
    eapply jacobian_eq_jac_eq.
    eapply jac_add_comm.
    eapply jac_eq_symm.
    eapply jac_eq_trans.
    eapply (add_base_abstract_jac_add_equiv _ _
      (groupMul_signedWindows_prog' wsize g p1
           (l1 ++ [wm_Double 1]))).
    eauto.
    eauto.
    symmetry.
    eapply H11.
    eapply IHls; eauto.
    inversion H1; clear H1; subst.
    trivial.
    inversion H1; clear H1; subst.
    intuition idtac.
    
    eapply jacobian_eq_jac_eq.
    eapply Jacobian.Proper_add.
    reflexivity.
    apply nth_error_map_ex in H4.
    destruct H4; intuition idtac; subst.
    erewrite nth_error_nth; eauto.
    unfold zDouble_n.
    rewrite Z.shiftl_mul_pow2.
    rewrite NPeano.Nat.mul_comm.
    reflexivity.
    apply Znat.Nat2Z.is_nonneg.
    
    discriminate.
    discriminate.
    discriminate.
    discriminate.

  Qed.

  
  Theorem ls_add_base_abstract_equiv : forall ls  rwnaf1 rwnaf2 x0 x n p1 p2,
    List.Forall (fun x => OddWindow wsize (sbvToInt _ x)) rwnaf2 -> 
    List.Forall (fun x => Nat.gcd x numPrecompExponentGroups = numPrecompExponentGroups) (List.map (fun x => x - n)%nat ls)  -> 
    List.Forall (fun x => x < Datatypes.length rwnaf2) ls -> 
    rwnaf1 = List.map (fun x => sbvToInt _ x) rwnaf2 -> 
    jac_eq (fromPoint p1) (seqToProd p2) ->
    multiSelect (signedWindowsToProg rwnaf1 0) ls = Some x0 ->
    decrExpLs n x0 = Some x -> 
    List.Forall2 (fun x y => Nat.div x numPrecompExponentGroups = Nat.div y numPrecompExponentGroups) ls (List.map (fun x => x - n)%nat ls) ->
    Datatypes.length rwnaf2 <= numPrecompExponentGroups * precompTableSize ->
    jac_eq
      (fromPoint
         (groupMul_signedWindows_prog' wsize g p1 x))
        (seqToProd
       (List.fold_left
          (add_base_abstract Fsquare Fmul Fsub Fadd Fopp base_precomp_table 1 numPrecompExponentGroups
             rwnaf2)
          (List.rev ls)
          p2)).

    induction ls; intros; simpl in *.
    inversion H0; clear H0; subst.
    simpl in *.
    unfold multiSelect in *.
    simpl in *.
    inversion H4; clear H4; subst.
    simpl in *.
    inversion H5; clear H5; subst.
    simpl in *.
    trivial.

    inversion H6; clear H6; subst.
    inversion H0; clear H0; subst.
    simpl in *.
    rewrite multiSelect_cons in *.
    optSomeInv.  
    simpl.
    rewrite fold_left_app.
    simpl.
 
    assert (exists x, nth_error (List.map (fun x : bitvector 16 => sbvToInt 16 x) rwnaf2) a0 = Some x /\ w = wm_Add a0 x).
    eapply nth_error_signedWindowsToProg_Some_add in H0.
    destruct H0.
    intuition idtac; subst.
    simpl.
    econstructor; intuition idtac; eauto.

    destruct H4.
    destruct H4.
    subst.
    simpl in *.
    destruct (Compare_dec.le_dec n a0).
    optSomeInv.
    simpl in *.
    eapply jac_eq_trans.
    eapply jacobian_eq_jac_eq.
    eapply jac_add_comm.
    eapply jac_eq_symm.
    eapply jac_eq_trans.
    eapply (add_base_abstract_jac_add_equiv _ _
      (groupMul_signedWindows_prog' wsize g p1
           (l1))).
    eauto.
    eauto.
    symmetry.
    eapply H11.
    eapply IHls; eauto.
    inversion H1; clear H1; subst.
    trivial.
    inversion H1; clear H1; subst.
    intuition idtac.
    
    eapply jacobian_eq_jac_eq.
    eapply Jacobian.Proper_add.
    reflexivity.
    apply nth_error_map_ex in H4.
    destruct H4; intuition idtac; subst.
    erewrite nth_error_nth; eauto.
    unfold zDouble_n.
    rewrite Z.shiftl_mul_pow2.
    rewrite NPeano.Nat.mul_comm.
    reflexivity.
    apply Znat.Nat2Z.is_nonneg.
    discriminate.

  Qed.

  Theorem point_mul_base_abstract_list_equiv_h : forall x p p1 p2 rwnaf1 rwnaf2,
    jac_eq (fromPoint p1) (seqToProd p2) ->
    rwnaf1 = List.map (fun x => sbvToInt _ x) rwnaf2 -> 
    List.Forall (OddWindow wsize) rwnaf1 ->
    groupMul_signedWindows_prog' wsize g p1 (flatten x) = p ->
    permuteAndDouble_grouped rwnaf1 1
       (groupIndices_h (S (S (S nw))) numPrecompExponentGroups (List.length x)) = Some x ->
  Datatypes.length rwnaf2 <= numPrecompExponentGroups * precompTableSize ->
    Datatypes.length rwnaf2 = (S (S (S nw))) -> 
    (Datatypes.length x) < (numPrecompExponentGroups) ->
  jac_eq (fromPoint p)
    (seqToProd
       (List.fold_left
          (double_add_base_abstract Fsquare Fmul Fsub Fadd Fopp base_precomp_table 1 wsize (S (S (S nw)))
             rwnaf2)
          (forNats (List.length x))
          p2
    )).

    induction x using rev_ind; intros; simpl in *; subst.
    trivial.

    rewrite app_length in *.
    simpl in *.

    rewrite NPeano.Nat.add_comm in *.      
    simpl in *.
    rewrite flatten_app in *.
    rewrite groupMul_signedWindows_prog'_app_equiv in *.
    simpl in *.
    rewrite app_nil_r in *.
    apply permuteAndDouble_grouped_app in H3.
    destruct H3.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H2.
    destruct H3.
    subst.
    assert (x0 = x1 /\ [x] = x3).
    unfold permuteAndDouble_grouped in H2. simpl in *.
    optSomeInv.
    simpl in *.
    optSomeInv.
    simpl in *.
    optSomeInv.
    eapply app_inj_tail in H7; intuition idtac; subst; trivial.

    destruct H8. subst.

    unfold permuteAndDouble_grouped in H2.
    simpl in *.
    optSomeInv.
    simpl in *.
    optSomeInv.
    simpl in *.
    optSomeInv.
    apply decrExpLs_app_if in H2.
    destruct H2.
    destruct H2.
    destruct H2.
    destruct H3.
    subst; simpl in *.
    optSomeInv.
    simpl in *.
    eapply IHx; try reflexivity.
    
    unfold double_add_base_abstract.
    destruct (PeanoNat.Nat.eq_dec (Datatypes.length x1) (Nat.pred (Nat.pred wsize))).
    unfold numPrecompExponentGroups in *.
    lia.
    
    eapply (@double_add_base_abstract_equiv _ _ _ _ _ (Datatypes.length x1)).
    eapply Forall_map; eauto.
    eapply Forall_map.
    eapply lsMultiples_gcd.
    eapply List.Forall_impl; [idtac | apply lsMultiples_length_weak].
    intros.
    simpl in *; subst.
    lia.
    reflexivity.
    trivial.
    eauto.
    rewrite NPeano.Nat.mul_1_r in *.
    trivial.
    apply Forall2_map_r.
    apply Forall2_same_Forall.
    apply lsMultiples_div.
    unfold numPrecompExponentGroups in *.
    lia.
    lia.
    lia.
    trivial.
    trivial.
    lia.
    lia.
    lia.

  Qed.

  Local Opaque jac_eq.

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

  Theorem point_mul_base_abstract_list_equiv : forall x p p2 rwnaf1 rwnaf2,
    jac_eq (fromPoint zero_point) (seqToProd p2) ->
    rwnaf1 = List.map (fun x => sbvToInt _ x) rwnaf2 -> 
    List.Forall (OddWindow wsize) rwnaf1 ->
    groupMul_signedWindows_prog' wsize g zero_point (flatten x) == p ->
    permuteAndDouble_grouped rwnaf1 1
       (groupIndices_h (S (S (S nw))) numPrecompExponentGroups (List.length x)) = Some x ->
  Datatypes.length rwnaf2 <= numPrecompExponentGroups * precompTableSize ->
  Datatypes.length rwnaf2 = (S (S (S nw))) ->
  (Datatypes.length x) <= (numPrecompExponentGroups) ->
  jac_eq (fromPoint p)
    (seqToProd
       (List.fold_left
          (double_add_base_abstract Fsquare Fmul Fsub Fadd Fopp base_precomp_table 1 wsize (S (S (S nw)))
             rwnaf2)
          (forNats (List.length x))
          p2
    )).

    intros.
    destruct (PeanoNat.Nat.eq_dec (Datatypes.length x) numPrecompExponentGroups).  
    replace (groupMul_signedWindows_prog' wsize g zero_point (flatten x))
      with (groupMul_signedWindows_prog_ls wsize g zero_point x) in *.
    
    eapply (@permuteAndDouble_grouped_no_double_equiv _ _ _ EC_CommutativeGroupWithDouble) in H3.
    destruct H3.
    destruct H3.
    eapply jac_eq_trans.
    eapply jacobian_eq_jac_eq.
    symmetry.
    eapply H2.
    eapply jac_eq_trans.
    eapply jacobian_eq_jac_eq.
    unfold idElem in *.
    eapply H7.

    destruct x using rev_ind; intros; simpl in *; subst.
    unfold numPrecompExponentGroups in *.
    lia.
    
    clear IHx.
    unfold permuteAndDouble_grouped' in *.
    rewrite app_length in *.
    simpl in *.
    rewrite NPeano.Nat.add_comm in *.      
    simpl in *.
    rewrite app_length in *.
    simpl in *.
    rewrite NPeano.Nat.add_comm in *.      
    simpl in *.
    optSomeInv.
    rewrite last_last in *.
    rewrite removelast_last in *.
    rewrite groupMul_signedWindows_prog_ls_equiv.
    rewrite flatten_app.
    rewrite groupMul_signedWindows_prog'_app_equiv.
    simpl.
    rewrite app_nil_r.

    assert ((Datatypes.length x1) = (Datatypes.length l1)).
    apply permuteAndDouble_grouped_length in H9.
    rewrite H9.
    rewrite groupIndices_h_length.
    reflexivity.
    rewrite H3.
    eapply (point_mul_base_abstract_list_equiv_h (groupMul_signedWindows_prog' wsize g zero_point l0)).
    unfold double_add_base_abstract.
    destruct (PeanoNat.Nat.eq_dec (Datatypes.length l1) (Nat.pred (Nat.pred wsize))). 

    eapply (@ls_add_base_abstract_equiv _ _ _ _ _  (Datatypes.length l1)).
    eapply Forall_map.
    trivial.
    eapply Forall_map.
    apply lsMultiples_gcd.
    eapply List.Forall_impl; [idtac | 
    apply lsMultiples_length_weak].
    intros.
    simpl in *; lia.
    reflexivity.
    trivial.
    rewrite <- H3.
    eauto.
    rewrite groupIndices_h_length in H8.
    rewrite <- H3.
    rewrite NPeano.Nat.mul_1_r in H8.
    trivial.
    apply Forall2_map_r.
    apply Forall2_same_Forall.
    eapply lsMultiples_div.
    lia.
    lia.
    lia.
    unfold numPrecompExponentGroups in *.
    lia.
    reflexivity.
    trivial.
    reflexivity.
    rewrite <- H3.
    trivial.
    lia.
    lia.
    lia.
    lia.
    assert (S (S (S nw)) <> 0)%nat by lia.
    eauto.
    assert (numPrecompExponentGroups <> 0)%nat.
    unfold numPrecompExponentGroups.
    lia.
    eauto.

    eapply groupMul_signedWindows_prog_ls_equiv.
    eapply jac_eq_trans.
    eapply jacobian_eq_jac_eq.
    symmetry.
    eapply H2.
    eapply point_mul_base_abstract_list_equiv_h; eauto.
    lia.

  Qed.

  Theorem groupIndices_length : forall n x,
    List.length (groupIndices n x) = x.

    intros.
    unfold groupIndices.
    apply groupIndices_h_length.
  Qed.

  Theorem mul_scalar_rwnaf_abstract_OddWindow : forall n,
     (bvToInt 384 n < 2 ^ Z.of_nat (S (S (S nw)) * wsize))%Z -> 
    List.Forall (OddWindow wsize) (List.map (fun x0 : bitvector 16 => sbvToInt 16 x0) (mul_scalar_rwnaf_abstract wsize nw n)).

    intros.
    specialize (mul_scalar_rwnaf_abstract_equiv n); intros.
    intuition idtac.
    eapply Forall_map.
    eapply forall2_symm in H3.

    specialize (@recode_rwnaf_correct wsize); intros.
    assert (wsize <> 0)%nat by lia.
    intuition idtac.
    specialize (H5 (S (S (S nw)))). 
    assert (S (S (S nw)) <> 0)%nat by lia.
    intuition idtac.

    eapply (Foralll2_impl (fun (y : bitvector 16)(z : Z) => y = intToBv _ z)) in H3.
    eapply forall2_map_eq in H3.
    rewrite H3.

    specialize (H6 (bvToNat _ n)).
    assert (BinInt.Z.of_nat (bvToNat 384 n) < BinInt.Z.shiftl 1 (BinInt.Z.of_nat (S (S (S nw)) * wsize)))%Z.
    rewrite Z.shiftl_1_l.
    rewrite bvToNat_toZ_equiv.
    eapply H.
    intuition idtac.
    rewrite bvToNat_toZ_equiv in *.
    unfold RegularReprOfNat, RegularReprOfZ in *.
    intuition idtac.  
    clear H8.
    unfold RegularWindows in *.
    eapply List.Forall_forall.
    intros.
    eapply in_map_iff in H7.
    destruct H7.
    intuition idtac.
    subst.
    specialize (H6 x0).
    intuition idtac.
    rewrite sbvToInt_intToBv_id.
    trivial.
    lia.
    unfold OddWindow, GroupMulWNAF.OddWindow in *.
    rewrite Z.shiftl_1_l in *.
    intuition idtac.
    apply Z.abs_lt in H8.
    intuition idtac.
    eapply (Z.le_trans _ (- 2 ^ BinInt.Z.of_nat wsize)).
    eapply (Z.opp_le_mono (2 ^ BinInt.Z.of_nat wsize)).
    eapply Z.pow_le_mono_r.
    lia.
    lia.
    lia.
    apply Z.abs_lt in H8.
    intuition idtac.
    eapply Z.lt_le_trans; eauto.
    eapply Z.pow_le_mono_r.
    lia.
    lia.

    intros.
    subst.
    symmetry.
    apply intToBv_sbvToInt_id.
  Qed.

  Theorem decrExp_ProgOddWindow: forall l l0 n x y z,
    decrExp n l = Some l0 ->
    ProgOddWindow x y z l -> 
    ProgOddWindow x y z l0.

    intros.
    unfold decrExp in *.
    destruct l.
    destruct (Compare_dec.le_dec n n0 ); optSomeInv.
    unfold ProgOddWindow in *; intuition idtac; subst.
    lia.
    discriminate.
    optSomeInv.
    trivial.
  Qed.

  Theorem decrExpLs_ProgOddWindow: forall l l0 n x y z,
    decrExpLs n l = Some l0 ->
    List.Forall (ProgOddWindow x y z) l -> 
    List.Forall (ProgOddWindow x y z) l0.

    induction l; intros; simpl in *; optSomeInv.
    econstructor.
    inversion H0; clear H0; subst.
    econstructor.
    eapply decrExp_ProgOddWindow; eauto.
    eapply IHl; eauto.

  Qed.

  Theorem decrExpsLs_ProgOddWindow: forall l l0 n x y z,
    decrExpsLs n l = Some l0 ->
    (forall v, List.In v l -> List.Forall (ProgOddWindow x y z) v) -> 
    (forall v, List.In v l0 -> List.Forall (ProgOddWindow x y z) v).

    induction l; intros; simpl in *;
    optSomeInv;
    simpl in *.
    intuition idtac.
    destruct H1; subst.
    eapply H0.
    intuition idtac.
    eapply combineOpt_In in H3; eauto.
    eapply in_map_iff in H3.
    destruct H3.
    destruct H1.
    eapply decrExpLs_ProgOddWindow; eauto.
    
  Qed.

  Theorem recode_rwnaf_OddWindow : forall nw n, 
    nw <> 0%nat -> 
    (Z.of_nat n < BinInt.Z.shiftl 1 (BinInt.Z.of_nat (nw * wsize)))%Z ->
    List.Forall (OddWindow wsize) (recode_rwnaf wsize nw (Z.of_nat n)).

    intros.   
    specialize (@recode_rwnaf_correct wsize); intros.
    assert (wsize <> 0)%nat by lia.
    intuition idtac.
    specialize (H5 nw0).
    intuition idtac.
    specialize (H1 n).
    intuition idtac.
    eapply List.Forall_forall.
    intros.
    eapply H5.
    eauto.

  Qed.

  Theorem mul_scalar_rwnaf_abstract_length: forall z,
    (bvToInt 384 z < 2 ^ Z.of_nat (S (S (S nw)) * wsize))%Z -> 
    List.length (mul_scalar_rwnaf_abstract wsize nw z) = (S (S (S nw))).

    intros.
    specialize (mul_scalar_rwnaf_abstract_equiv z); intros.
    apply H0 in H.
    apply Forall2_length in H.
    rewrite <- H.
    apply recode_rwnaf_length.
    lia.
    lia.
  Qed.

  Theorem jac_eq_fromPoint_opp : forall x y,
    jac_eq (seqToProd x) (fromPoint y) -> 
    jac_eq
  (seqToProd
     (EC_P384_Abstract.point_opp Fopp x)) (fromPoint (Jacobian.opp y)).

    intros.
    eapply jac_eq_symm.
    eapply jac_eq_trans.
    eapply point_opp_equiv.
    eapply point_opp_jac_eq_proper.
    rewrite seqToProd_inv.
    eapply jac_eq_symm.
    trivial.

  Qed.

  Theorem nth_order_opp_eq : forall n p (pf : n < 3),
    n <> 1%nat ->
    nth_order (EC_P384_Abstract.point_opp Fopp p) pf = nth_order p pf.

    intros.
    unfold EC_P384_Abstract.point_opp.
    unfold EC_P384_Abstract.point in *.
    destructVec.
    repeat erewrite sawAt_nth_equiv; try lia.
    simpl.
    unfold nth_order.
    destruct n.
    reflexivity.
    destruct n. lia.
    destruct n.
    reflexivity.
    lia.
  
  Qed.

  Theorem nth_order_append_vec_lt : forall (A : Type) n1 n2 (v1 : Vec n1 A)(v2 : Vec n2 A) x (pf1 : x < n1 + n2)(pf2 : x < n1),
    nth_order (Vector.append v1 v2) pf1 = nth_order v1 pf2.

    induction v1; intros; simpl in *.
    lia.
    destruct x; simpl in *.
    rewrite nth_order_0_cons.
    rewrite nth_order_0_cons.
    reflexivity.
    erewrite nth_order_S_cons.
    erewrite nth_order_S_cons.
    eapply IHv1.

    Unshelve.
    lia.
    lia.

  Qed.

  Theorem nth_order_append_vec_ge : forall (A : Type) n1 n2 (v1 : Vec n1 A)(v2 : Vec n2 A) x (pf1 : x < n1 + n2)(pf2 : (x - n1) < n2),
    x >= n1 -> 
    nth_order (Vector.append v1 v2) pf1 = nth_order v2 pf2.

    induction v1; intros; simpl in *.
    destruct x; simpl in *.
    eapply VectorSpec.nth_order_ext.
    eapply VectorSpec.nth_order_ext.

    destruct x; simpl in *.
    lia.
    eapply IHv1.
    lia.

  Qed.

  Theorem point_mul_base_abstract_model_equiv : forall n x,
    (bvToInt 384 n < 2 ^ Z.of_nat (S (S (S nw)) * wsize))%Z ->
    groupedMul_scalar_precomp numPrecompExponentGroups wsize (S (S (S nw))) 1 (bvToNat _ n) = Some x ->
    S (S (S nw)) < numPrecompExponentGroups * precompTableSize -> 
    jac_eq (fromPoint x)
  (seqToProd
     (point_mul_base_abstract Fsquare Fmul Fsub Fadd Fopp base_precomp_table affine_default 1 wsize (S (S (S nw))) n)).

    intros.
    unfold point_mul_base_abstract, groupedMul_scalar_precomp in *.
    optSomeInv.
    unfold conditional_subtract_if_even_mixed_abstract.
    unfold groupedMul_precomp in *.
    optSomeInv.
    eapply permuteAndDouble_grouped_equiv_if in H3.
    destruct H3.
    intuition idtac; subst.
    unfold permuteAndDouble_grouped in *.
    optSomeInv.
    assert (List.length l0 = numPrecompExponentGroups).
    rewrite <- (@decrExpsLs_length 1 l l0); eauto.
    erewrite <- combineOpt_length; eauto.
    rewrite map_length.
    apply groupIndices_length.

    replace (Nat.pred (Nat.pred (Nat.pred (S (S (S nw)))))) with nw.

    assert (jac_eq (fromPoint p)
  (seqToProd
     (List.fold_left
        (double_add_base_abstract Fsquare Fmul Fsub Fadd Fopp base_precomp_table 1 wsize 
           (S (S (S nw))) (mul_scalar_rwnaf_abstract wsize nw n))
        (forNats numPrecompExponentGroups) (replicate 3 (Vec 6 (bitvector 64)) (replicate 6 (bitvector 64) (intToBv 64 0)))))).
    unfold numPrecompExponentGroups in *.
    rewrite <- H4.
    replace (Datatypes.length l0) with (Datatypes.length (List.map (fun x => x ++ [wm_Double 1]) l0)).
    eapply point_mul_base_abstract_list_equiv.
    apply zero_point_jac_eq.
 
    reflexivity.
    apply mul_scalar_rwnaf_abstract_OddWindow.
    lia.
    rewrite (@groupMul_signedWindows_prog'_equiv _ _ _ EC_CommutativeGroupWithDouble).
    eapply groupMul_signedWindows_precomp_equiv.
    apply (fun x => True).
    lia.
    assert ((S (S (S nw))) <> 0)%nat by lia; eauto.
    assert (numPrecompExponentGroups <> 0)%nat. unfold numPrecompExponentGroups. lia. eauto.
    apply pExpMultiple_correct.
    eapply Forall_flatten.
    intros.
    eapply in_map_iff in H6.
    destruct H6.
    intuition idtac; subst.
    eapply Forall_app.
    intuition idtac.
    eapply decrExpsLs_ProgOddWindow; eauto.
    intros.
    eapply combineOpt_In in H3; eauto.
    apply in_map_iff in H3.
    destruct H3.
    intuition idtac.
    eapply multiSelect_OddWindow; [idtac | eapply H7].
    eapply signedWindowsToProg_ProgOddWindow.
    apply (fun x => True).
    lia.
    assert (S (S (S nw)) <> 0)%nat.
    lia.
    eauto.
    unfold numPrecompExponentGroups.
    lia.
    rewrite recode_rwnaf_length.
    unfold numPrecompExponentGroups in *.
    lia.
    lia.
    lia.
    apply recode_rwnaf_OddWindow.
    lia.
    rewrite bvToNat_toZ_equiv.
    rewrite Z.shiftl_1_l.
    eauto.
    econstructor.   
    unfold ProgOddWindow; simpl.
    trivial.
    econstructor.
    
    eauto.
    unfold permuteAndDouble_grouped.
    rewrite map_length.
    unfold groupIndices in *.
    rewrite H4.
    
    specialize (@mul_scalar_rwnaf_abstract_equiv n); intros.
    intuition idtac.
    apply forall2_map_eq in H7.
    rewrite <- bvToNat_toZ_equiv in H7.
    rewrite H7 in H3.
    replace (combineOpt
    (List.map
       (multiSelect
          (signedWindowsToProg (List.map (fun x : bitvector 16 => sbvToInt 16 x) (mul_scalar_rwnaf_abstract wsize nw n)) 0))
       (groupIndices_h (S (S (S nw))) numPrecompExponentGroups (Nat.pred wsize))))
      with
    (combineOpt
      (List.map (multiSelect (signedWindowsToProg (List.map (sbvToInt 16) (mul_scalar_rwnaf_abstract wsize nw n)) 0))
         (groupIndices_h (S (S (S nw))) (Nat.pred wsize) (Nat.pred wsize))) ).
    rewrite H3.
    rewrite H5.
    reflexivity.
    reflexivity.
    rewrite mul_scalar_rwnaf_abstract_length.
    unfold numPrecompExponentGroups in *.
    lia.
    lia.
    rewrite mul_scalar_rwnaf_abstract_length.
    reflexivity.
    lia.

    rewrite map_length.
    unfold numPrecompExponentGroups in *.
    lia.
    rewrite map_length.
    reflexivity.

    case_eq (Nat.even (bvToNat 384 n)); intros.
    rewrite H7 in H0.
    optSomeInv.
    eapply point_add_mixed_eq.
    rewrite nth_order_opp_eq; try lia.
    
    unfold affine_g.
    remember (List.nth 0 (List.nth 0 base_precomp_table []) affine_default) as z.
    erewrite (@nth_order_append_vec_ge _ 2%nat 1%nat z).
    rewrite nth_order_0_cons.
    eauto.
    lia.
    
    eauto.
    unfold affine_g.
    eapply jac_eq_symm.
    eapply jac_eq_fromPoint_opp.
    replace ((Vector.append
        (List.nth 0 (List.nth 0 base_precomp_table []) affine_default)
        (cons felem 1 0 (nil felem))))
    with
    (affineToJac (List.nth 0 (List.nth 0 base_precomp_table []) affine_default)).
    
    eapply jac_eq_trans.
    eapply base_precomp_table_correct.
    lia.
    unfold numPrecompExponentGroups.
    specialize (PeanoNat.Nat.pow_nonzero 2 (Nat.pred wsize)).
    intuition idtac.
    lia.
    rewrite NPeano.Nat.mul_0_r.
    rewrite NPeano.Nat.mul_0_l.
    simpl.
    eapply jacobian_eq_jac_eq.
    rewrite jac_add_comm.
    apply jac_add_id_l.
    generalize (List.nth 0 (List.nth 0 base_precomp_table []) affine_default); intros.
    unfold affineToJac.
    specialize (@SAWCorePrelude_proofs.rewrite_append _ _ _ (cons F 1 0 (nil F)) _ a0); intros.
    apply inj_pair2 in H0.
    unfold felem, F in *.
    simpl in *.
    unfold Vec in *.
    unfold Bool in *.
    eapply eq_trans.
    eapply H0.
    reflexivity.

    rewrite H7 in H0.
    optSomeInv.
    eauto.

    Unshelve.
    lia.
    lia.

  Qed.

  Theorem groupMul_S_opp : forall x p,
    Jacobian.eq (groupMul x p) (Jacobian.add (groupMul (S x) p) (Jacobian.opp p)).

    intros.
    simpl in *.
    rewrite jac_add_comm.
    rewrite <- jac_add_assoc.
    symmetry.
    transitivity (Jacobian.add zero_point (groupMul x p)).
    eapply Jacobian.Proper_add.
    rewrite jac_add_comm.
    apply jac_opp_correct.
    reflexivity.
    apply jac_add_id_l.

  Qed.

  Definition pMultiple(z : Z) : point := pExpMultiple 0%nat z.
  Theorem pMultiple_correct : forall w,
    OddWindow wsize w ->
    pMultiple w == groupMul_doubleAdd_signed w g.

    intros.
    unfold pMultiple.
    rewrite pExpMultiple_correct; eauto.
    rewrite PeanoNat.Nat.mul_0_r.
    simpl.
    reflexivity.
    lia.

  Qed.

  Theorem groupedMulScalar_precomp_groupMul_equiv : forall n p,
    (bvToInt _ n < 2 ^ (Z.of_nat (S (S (S nw)) * wsize))%nat)%Z ->
    S (S (S nw)) < numPrecompExponentGroups * precompTableSize -> 
    groupedMul_scalar_precomp numPrecompExponentGroups wsize (S (S (S nw))) 1 (bvToNat 384 n) = Some p ->
    jac_eq (fromPoint (groupMul (bvToNat 384 n) g)) (fromPoint p).

    intros.
    unfold groupedMul_scalar_precomp in *.
    optSomeInv.

    case_eq (groupedMul wsize (S (S (S nw))) g numPrecompExponentGroups 1
       (recode_rwnaf wsize (S (S (S nw))) (Z.of_nat (bvToNat 384 n)))); intros.
    assert  (p0 == p1).
    eapply groupedMul_precomp_equiv; [idtac | idtac | idtac | idtac | idtac | idtac | idtac | eauto | eauto].
    apply (fun x => True).
    lia.
    lia.
    unfold numPrecompExponentGroups. lia.
    eapply pExpMultiple_correct.
    rewrite recode_rwnaf_length.
    lia.
    lia.
    lia.
    eapply recode_rwnaf_OddWindow.
    lia.
    rewrite bvToNat_toZ_equiv.
    rewrite Z.shiftl_1_l.
    eauto.

    assert (groupMul_signedWindows wsize pMultiple (recode_rwnaf wsize (S (S (S nw))) (Z.of_nat (bvToNat 384 n))) == p1).
    eapply groupedMul_correct.
    lia.
    assert (S (S (S nw)) <> 0)%nat.
    lia.
    eauto.
    assert (numPrecompExponentGroups <> 0)%nat. unfold numPrecompExponentGroups. lia.
    eauto.
    eapply pMultiple_correct.
    apply recode_rwnaf_length.
    lia.
    lia.
    apply recode_rwnaf_OddWindow.
    lia.
    rewrite bvToNat_toZ_equiv.
    rewrite Z.shiftl_1_l.
    eauto.
    eauto.

    assert (groupMul_signedWindows wsize pMultiple
     (recode_rwnaf wsize (S (S (S nw))) (Z.of_nat (bvToNat 384 n))) ==
    groupMul_doubleAdd_signed (windowsToZ wsize (recode_rwnaf wsize (S (S (S nw))) (Z.of_nat (bvToNat 384 n)))) g).
    eapply groupMul_signedWindows_correct.
    apply pMultiple_correct.
    apply recode_rwnaf_OddWindow.
    lia.
    rewrite bvToNat_toZ_equiv.
    rewrite Z.shiftl_1_l.
    eauto.

    case_eq (Nat.even (bvToNat 384 n)); intros;
    rewrite H7 in H1.
    replace (windowsToZ wsize (recode_rwnaf wsize (S (S (S nw))) (Z.of_nat (bvToNat 384 n)))) with (Z.of_nat (S (bvToNat 384 n))) in *.

    assert (groupMul_doubleAdd_signed (BinInt.Z.of_nat (S (bvToNat 384 n))) g ==
      groupMul (S(bvToNat 384 n)) g).
    eapply groupMul_signed_correct.

    optSomeInv.
    eapply jacobian_eq_jac_eq.
    assert (Jacobian.eq (groupMul (bvToNat 384 n) g) (Jacobian.add (groupMul (S(bvToNat 384 n)) g)  (Jacobian.opp g))).
    apply groupMul_S_opp.
    rewrite H1.
    eapply Jacobian.Proper_add.
    rewrite H4.
    rewrite <- H8.
    rewrite <- H6.
    eapply H5.
    reflexivity.

    symmetry.
    assert (RegularReprOfZ wsize (recode_rwnaf wsize (S (S (S nw))) (Z.of_nat (bvToNat 384 n))) (Z.of_nat (bvToNat 384 n)) ).
    eapply recode_rwnaf_correct.
    lia.
    lia.
    rewrite Z.shiftl_mul_pow2.
    rewrite Z.mul_1_l.
    rewrite bvToNat_toZ_equiv.
    eauto.
    lia.
    unfold RegularReprOfZ in *.
    intuition idtac.
    erewrite even_of_nat_equiv in H7.
    rewrite <- Z.negb_even in H10.
    rewrite H7 in H10.
    Local Opaque recode_rwnaf.
    simpl in *.
    rewrite H10.
    rewrite Znat.Zpos_P_of_succ_nat.
    reflexivity.
    eauto.

    replace (windowsToZ wsize (recode_rwnaf wsize (S (S (S nw))) (Z.of_nat (bvToNat 384 n)))) with (Z.of_nat (bvToNat 384 n)) in *.

    assert (groupMul_doubleAdd_signed (BinInt.Z.of_nat (bvToNat 384 n)) g ==
      groupMul (bvToNat 384 n) g).
    eapply groupMul_signed_correct.

    optSomeInv.
    eapply jacobian_eq_jac_eq.
    symmetry.
    rewrite H4.
    rewrite <- H5.
    rewrite H6.
    eapply H8.

    symmetry.
    assert (RegularReprOfZ wsize (recode_rwnaf wsize (S (S (S nw))) (Z.of_nat (bvToNat 384 n))) (Z.of_nat (bvToNat 384 n)) ).
    eapply recode_rwnaf_correct.
    lia.
    lia.
    rewrite Z.shiftl_mul_pow2.
    rewrite Z.mul_1_l.
    rewrite bvToNat_toZ_equiv.
    eauto.
    lia.
    unfold RegularReprOfZ in *.
    intuition idtac.
    erewrite even_of_nat_equiv in H7.
    rewrite <- Z.negb_even in H10.
    rewrite H7 in H10.
    Local Opaque recode_rwnaf.
    simpl in *.
    rewrite H10.
    reflexivity.
    eauto.
    
    exfalso.
    eapply groupedMul_precomp_groupedMul_Some; [idtac | idtac | eauto | eauto].
    rewrite recode_rwnaf_length.
    eauto.
    lia.
    lia.
    eapply recode_rwnaf_OddWindow.  
    lia.
    rewrite bvToNat_toZ_equiv.
    rewrite Z.shiftl_1_l.
    eauto.

  Qed.

  Theorem point_mul_base_abstract_correct : forall n x,
    (bvToInt 384 n < 2 ^ Z.of_nat (S (S (S nw)) * wsize))%Z ->
    S (S (S nw)) < numPrecompExponentGroups * precompTableSize -> 
    (groupedMul_scalar_precomp numPrecompExponentGroups wsize (S (S (S nw))) 1 (bvToNat 384 n)) = Some x -> 
    jac_eq (fromPoint (groupMul (bvToNat 384 n) g))
   (seqToProd (point_mul_base_abstract Fsquare Fmul Fsub Fadd Fopp base_precomp_table affine_default 1 wsize (S (S (S nw))) n)).

    intros.

    eapply jac_eq_trans; [idtac | eapply point_mul_base_abstract_model_equiv]; eauto.
    eapply groupedMulScalar_precomp_groupMul_equiv; eauto.

  Qed.


  Definition decrExp'(n : nat) (n' : nat) :=  if Compare_dec.le_dec n n' then Some (n' - n)%nat else None.

  Fixpoint decrExpLs' (n : nat) (ps : list nat)  :=
  match ps with
  | [] => Some []
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
  | [] => Some []
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
    edestruct (@nth_error_Some_ex  _ a0 (signedWindowsToProg ws 0)).
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
    destruct (Compare_dec.le_dec 1 a0).
    optSomeInv.   
    unfold decrExp.
    destruct (Compare_dec.le_dec 1 a0).
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
    apply (@Forall_Forall2_impl _ _ _ a0) in H6.
    eapply (@Forall2_Forall_impl _ _ _ b0).
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

  Theorem groupMul_signedWindows_precomp_Some : forall x, 
    List.Forall (wmIsMultiple 4) x ->
    exists y,
    groupMul_signedWindows_precomp 5 g 4 pExpMultiple zero_point x = Some y.

    induction x; intros; simpl in *.
    econstructor.
    intros.
    reflexivity.

    inversion H; clear H; subst.
    destruct IHx; trivial.
    rewrite H.
    unfold evalWindowMult_precomp.
    destruct a0.
    destruct (divides 4 n).
    econstructor.
    intros.
    reflexivity.
    unfold wmIsMultiple in H2.
    rewrite NPeano.Nat.gcd_comm in n0.
    intuition idtac.
    
    econstructor.
    reflexivity.

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

  Theorem groupedMul_scalar_precomp_Some_P384_concrete : forall n, exists x, 
    groupedMul_scalar_precomp 4 5 77 1 n = Some x.

    intros.
    unfold groupedMul_scalar_precomp.
    unfold groupedMul_precomp.

    assert  (exists x, permuteAndDouble_grouped (recode_rwnaf 5 77 (Z.of_nat n)) 1 (groupIndices 77 4) = Some x /\
        List.Forall (List.Forall (wmIsMultiple 4)) x).
    eapply permuteAndDouble_grouped_Some.
    apply groupIndices_all_lt.
    rewrite groupIndices_length. reflexivity.
    reflexivity.
    repeat econstructor.

    destruct H.
    destruct H.
    erewrite permuteAndDouble_grouped_equiv; eauto.
    edestruct (groupMul_signedWindows_precomp_Some).
    eapply Forall_flatten.
    intros.
    eapply (@List.Forall_forall _ _ x).
    trivial.
    eauto.
    
    unfold idElem.
    simpl.
    rewrite H1.
    destruct (Nat.even n); econstructor; eauto.

  Qed.

  End PointMulAbstract.

   (**
  The point multiplication spec extracted from Cryptol is equivalent to the basic group
  multiplication operation on points. 
  *)
  Theorem point_mul_correct : forall (p : point) (n : seq 384 Bool),
      jac_eq (fromPoint (groupMul (bvToNat _ n) p))
      (seqToProd (point_mul (prodToSeq (fromPoint p)) n)).

    intros.
    unfold point_mul.
    rewrite point_mul_abstract_equiv.
    eapply jac_eq_trans; [idtac | eapply point_mul_abstract_signedRegular_equiv].
    unfold groupMul.
    eapply jacobian_eq_jac_eq.

    rewrite groupMul_signedRegular_table_correct.
    reflexivity.

    lia.
    lia.

    eapply Z.lt_le_trans.
    apply bvToNat_lt_word.
    rewrite Z.shiftl_1_l.
    eapply Z.pow_le_mono_r.
    lia.
    lia.
    lia.
    lia.
    eapply Z.lt_le_trans.
    apply bvToNat_lt_word.
    rewrite Z.shiftl_1_l.
    eapply Z.pow_le_mono_r.
    lia.
    lia.

  Qed.

  (**
  The base point multiplication spec extracted from Cryptol is equivalent to the basic group
  multiplication operation on the base point. 
  *)
  Definition preCompTable := (List.map (fun x => to_list x) (to_list p384_g_pre_comp)).

  Section PointMulBase.
  Variable g : point.

  Hypothesis preCompTable_on_curve: forall (ls : list affine_point) (p : affine_point), List.In p ls -> List.In ls preCompTable -> on_curve p.

  Definition wsize := 5.
  Hypothesis preCompTable_correct : forall n1 n2,
    (n1 < List.length preCompTable)%nat ->
    (n2 < Nat.pow 2 (numPrecompExponentGroups wsize))%nat-> 
    jac_eq (seqToProd (affineToJac (List.nth n2 (List.nth n1 preCompTable List.nil) (affine_default preCompTable)))) (fromPoint (groupMul ((2 * n2 + 1) * (Nat.pow 2 (n1 * (numPrecompExponentGroups wsize) * wsize))) g)).

  Theorem to_list_entry_length_h : forall (A : Type)(n2 : nat)(v : list (Vec n2 A)) (ls : list A),
    List.In ls (List.map (fun x => to_list x) v) ->
    List.length ls = n2.

    induction v; intros.
    simpl in H.
    intuition idtac.

    simpl in H.
    intuition idtac.
    subst.
    apply length_to_list.
    eapply IHv.
    eauto.

  Qed.
 
  Theorem to_list_entry_length : forall (A : Type)(n1 n2 : nat)(v : Vec n1 (Vec n2 A)) (ls : list A),
    List.In ls (List.map (fun x => to_list x) (to_list v)) ->
    List.length ls = n2.

    intros.
    eapply to_list_entry_length_h.
    eauto.

  Qed.

  Theorem preCompTable_entry_length : forall ls,
    List.In ls preCompTable ->
    Datatypes.length ls = Nat.pow 2 (numPrecompExponentGroups wsize).

    intros.
    unfold preCompTable in *.
    erewrite to_list_entry_length; eauto.

  Qed.

  Theorem preCompTable_length : 
    Datatypes.length preCompTable = 20%nat.

    intros.
    reflexivity.

   Qed.

  (* Assume the multiplicative identity element of the field is equal to the hard-coded "one" value in the code. *)
  Hypothesis Fone_eq : 
    p384_felem_one = 1.

  (* The base point multiplication operation using a hard-coded table is equivalent to multiplication by the base point. *)
  Theorem point_mul_base_correct : forall (n : seq 384 Bool),
      jac_eq 
        (fromPoint (groupMul (bvToNat _ n) g))
        (seqToProd (point_mul_base n)).

    intros.
    assert ( Datatypes.length preCompTable <> 0%nat).
    pose proof preCompTable_length.
    lia.
    edestruct (groupedMul_scalar_precomp_Some_P384_concrete); eauto.
    unfold point_mul_base.
    assert (1 < wsize < 16)%nat.
    unfold wsize; lia.
    assert (List.Forall2 (fun (x : list affine_point) (y : t affine_point 16) => x = to_list y) preCompTable
         (to_list p384_g_pre_comp)).
    unfold preCompTable.
    eapply Forall2_map_l.
    eapply Forall2_same_Forall.
    eapply List.Forall_impl; [idtac | eapply Forall_I].
    intros.
    trivial.
    eauto.

    rewrite (@point_mul_base_abstract_equiv _ _ _ _ _ preCompTable H2 (affine_default preCompTable)).
    rewrite Fone_eq.
    eapply point_mul_base_abstract_correct; eauto.
    eapply Z.lt_le_trans.
    eapply bvToInt_bound.
    apply Z.pow_le_mono_r.
    lia.
    simpl.
    lia.

    unfold precompTableSize.
    match goal with 
    | [ |- (_ < _ * ?a)%nat] => replace a with 20%nat
    end.
    unfold numPrecompExponentGroups, wsize.
    simpl; lia.
    symmetry.
    apply preCompTable_length.

    Unshelve.
    lia.
    lia.
    match goal with 
    | [ |- (?a <> 0)%nat] => replace a with 20%nat
    end.
    lia.
    symmetry.
    apply preCompTable_length.
    apply preCompTable_entry_length.
    eauto.

  Qed.

  End PointMulBase.

End ECEqProof.

