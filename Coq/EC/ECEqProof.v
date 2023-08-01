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
From EC Require Import Zfacts.
From EC Require Import EC_P384_5.
From EC Require Import EC_P384_Abstract.
From EC Require Import CryptolToCoq_equiv.

Set Implicit Arguments.

Require Import CryptolToCoq.SAWCoreVectorsAsCoqVectors.

Section ECEqProof.

  Definition F := seq 6 (seq 64 Bool).

  Definition Fzero : F := (replicate 6 _ (replicate 64 _ false)).
  Variable Fone  : F.
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

  Variable Fsquare : F -> F.

  Definition point_add := point_add Fsquare Fmul Fsub Fadd.
  Definition point_add_jac := point_add false.

  Definition point_add_jac_prod (p1 p2 : (F * F * F)) : (F * F * F) :=
    let p3 := point_add_jac (prodToSeq p1) (prodToSeq p2) in
    (seqToProd p3).


  (* Assume that squaring satisifes its spec. *)
  Hypothesis felem_sqr_spec : forall (x : F), Fsquare x = Fmul x x.

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
      repeat rewrite felem_sqr_spec.
      unfold sawAt, atWithDefault. simpl.
      unfold nth_order, nth. simpl.

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

  Definition groupMul := @groupMul point Jacobian.add zero_point.
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

  Theorem preCompTable_h_cons : forall tsize p ls p2, 
    ls <> List.nil -> 
    (preCompTable_h Jacobian.add zero_point tsize (p :: ls) p2) = 
    p :: (preCompTable_h Jacobian.add zero_point tsize ls p2).

      induction tsize; unfold preCompTable_h in *; intuition; simpl in *.
      rewrite <- IHtsize.
      destruct ls; simpl in *. intuition.
      reflexivity.
      intuition.
      eapply app_cons_not_nil.
      symmetry.
      eauto.

  Qed.
  
  Theorem recode_rwnaf_bound_In : forall wsize numWindows x z,
    (wsize <> 0)%nat ->
    (numWindows <> 0)%nat ->
    (BinInt.Z.of_nat x < BinInt.Z.shiftl 1 (BinInt.Z.of_nat (numWindows * wsize)))%Z ->
    List.In z (recode_rwnaf wsize numWindows (Z.of_nat x)) ->
    (-2^(Z.of_nat wsize) < z < (2^(Z.of_nat wsize)))%Z.

    intros.
    apply Z.abs_lt.
    rewrite <- Z.shiftl_1_l.
    eapply (@recode_rwnaf_correct wsize _ numWindows); eauto.

    Unshelve.
    lia.

  Qed.

  Theorem recode_rwnaf_bound_nth : forall n wsize numWindows x,
    (wsize <> 0)%nat ->
    (numWindows <> 0)%nat ->
    (BinInt.Z.of_nat x < BinInt.Z.shiftl 1 (BinInt.Z.of_nat (numWindows * wsize)))%Z ->
    (-2^(Z.of_nat wsize) < (List.nth n
   (recode_rwnaf wsize numWindows (Z.of_nat x)) 0) < (2^(Z.of_nat wsize)))%Z.

    intros.
    destruct (PeanoNat.Nat.lt_decidable n numWindows).
    eapply recode_rwnaf_bound_In; eauto.
    apply nth_In.
    rewrite recode_rwnaf_length; lia.

    rewrite nth_overflow.
    intuition idtac.
    apply Z.opp_neg_pos.
    apply Z.pow_pos_nonneg; lia.
    apply Z.pow_pos_nonneg; lia.
    rewrite recode_rwnaf_length; lia.

  Qed.

  
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

  Theorem mul_scalar_rwnaf_abstract_equiv : forall nw wsize z,
    0 < wsize < 16 ->
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
    rewrite H1.
    trivial.
    assert (BinInt.Z.succ (bvToInt 384%nat z) <> 2 ^ Z.of_nat (S (S (S nw)) * wsize))%Z.
    intuition idtac.
    rewrite H4 in H3.
    rewrite <- Z.negb_even in H3.
    rewrite Z.even_pow in H3.
    simpl in *.
    discriminate.
    lia.
    lia.
    rewrite <- Z.negb_odd.
    rewrite H1.
    trivial.
    lia.
    rewrite bvOr_bvToInt_equiv.
    rewrite bvToInt_intToBv_id.
    reflexivity.
    lia.

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

  Theorem map_bvAdd_0 : forall n ls,
    (List.map (bvAdd n (bvNat n 0%nat)) ls) = ls.

    induction ls; intros; simpl in *.
    reflexivity.
    rewrite IHls.
    f_equal.
    apply bvAdd_id_l.

  Qed.

  Theorem bvector_eq_dec : forall n (v1 v2 : VectorDef.t bool n),
    {v1 = v2} + {v1 <> v2}.

    intros.
    apply (Vector.eq_dec _ Bool.eqb).
    intros.
    apply Bool.eqb_true_iff.

  Defined.
   

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

  Theorem groupDouble_n_zero : forall n,
    groupDouble_n Jacobian.double n zero_point == zero_point.

    induction n; intros; simpl in *.
    reflexivity.
    transitivity (Jacobian.double zero_point).
    eapply Jacobian.Proper_double.
    eauto.
    rewrite jac_double_correct.
    rewrite jac_add_id_l.
    reflexivity.
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
      (preCompTable Jacobian.add zero_point Jacobian.double w p)
      (pre_comp_table_abstract (Nat.pred (Nat.pred (tableSize w))) (prodToSeq (fromPoint p))).

    intros.
    unfold preCompTable, preCompTable_h, pre_comp_table_abstract, EC_P384_Abstract.pre_comp_table_abstract.
    rewrite (@fold_left_scanl_equiv _ _ _ (fun a b => (Jacobian.add (Jacobian.double p) a))).
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


  Theorem groupDouble_n_double_comm : forall n (a1 : point),
    Jacobian.eq
  (Jacobian.double (groupDouble_n Jacobian.double n a1))
  (groupDouble_n Jacobian.double n (Jacobian.double a1)).

    induction n; intros; simpl in *.
    reflexivity.
    apply Jacobian.Proper_double.
    eapply IHn.
  
  Qed.


  Theorem groupDouble_n_fold_left_double_equiv : forall ws ls a1 a2,
    List.length ls = ws ->
    jac_eq (fromPoint a1) (seqToProd a2) ->
    jac_eq
  (fromPoint (groupDouble_n Jacobian.double ws a1))
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
    eapply groupDouble_n_double_comm.
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

  Theorem nat_shiftl_gt_base : forall n2 n1,
    (0 < n2 ->
    0 < n1 ->
    n1 < Nat.shiftl n1 n2).

    induction n2; intros; simpl in *.
    lia.
    destruct n2.
    simpl.
    unfold Nat.double.
    lia.
    assert (n1 < Nat.shiftl n1 (S n2)).
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

  Theorem Forall2_length_eq : forall (A B : Type)(lsa : list A)(lsb : list B) P,
    List.Forall2 P lsa lsb ->
    List.length lsa = List.length lsb.

    induction 1; intros; simpl in *; intuition idtac.
    congruence.

  Qed.

  Theorem mul_body_equiv : forall pred_wsize p a1 a2 b1 b2,
    0 < pred_wsize < 15 ->
    jac_eq (fromPoint a1) (seqToProd a2) ->
    b1 = sbvToInt 16 b2 ->
    (- 2 ^ Z.of_nat (S pred_wsize) < b1 < 2 ^ Z.of_nat (S pred_wsize))%Z ->
    jac_eq
      (fromPoint
         (groupMul_signedWindows_fold_body Jacobian.add Jacobian.double
            (S pred_wsize)
            (fun x : Z =>
             if (x <? 0)%Z
             then
              Jacobian.opp
                (List.nth
                   (BinInt.Z.to_nat (BinInt.Z.shiftr (BinInt.Z.abs x) 1))
                   (preCompTable Jacobian.add zero_point Jacobian.double
                      (S pred_wsize) p) zero_point)
             else
              List.nth
                (BinInt.Z.to_nat (BinInt.Z.shiftr (BinInt.Z.abs x) 1))
                (preCompTable Jacobian.add zero_point Jacobian.double
                   (S pred_wsize) p) zero_point) a1 b1))
      (seqToProd
         (double_add_body_abstract Fsquare Fmul Fsub Fadd Fopp pred_wsize
            (EC_P384_Abstract.pre_comp_table_abstract Fsquare Fmul Fsub
               Fadd (Nat.pred (Nat.pred (tableSize (S pred_wsize))))
               (prodToSeq (fromPoint p))) a2 b2)).

    intros.
    unfold double_add_body_abstract.

    rewrite select_point_abstract_nth_equiv.
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

    erewrite <- Forall2_length_eq; [idtac | eapply preCompTable_equiv].
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

  Theorem In_tl : forall (A : Type)(ls : list A) a,
    List.In a (List.tl ls) ->
    List.In a ls.

    intros.
    destruct ls; simpl in *.
    intuition idtac.
    intuition idtac.

  Qed.

  Theorem point_mul_abstract_signedRegular_cases : forall wsize numWindows n p,
    1 < wsize < 16 ->
    (BinInt.Z.of_nat (bvToNat 384%nat n) <
   BinInt.Z.shiftl 1 (BinInt.Z.of_nat (S (S (S numWindows)) * wsize)))%Z->
      jac_eq
    (seqToProd
       (List.fold_left
          (double_add_body_abstract Fsquare Fmul Fsub Fadd Fopp (Nat.pred wsize)
             (EC_P384_Abstract.pre_comp_table_abstract Fsquare Fmul
                Fsub Fadd (Nat.pred (Nat.pred (tableSize wsize)))
                (prodToSeq (fromPoint p))))
          (skipn 1
             (List.rev (mul_scalar_rwnaf_abstract wsize numWindows n)))
          (select_point_abstract
             (sign_extend_16_64
                (bvSShr 15
                   (List.nth (S (S numWindows))
                      (mul_scalar_rwnaf_abstract wsize numWindows n)
                      (bvNat 16 0%nat)) 1))
             (EC_P384_Abstract.pre_comp_table_abstract Fsquare Fmul
                Fsub Fadd (Nat.pred (Nat.pred (tableSize wsize)))
                (prodToSeq (fromPoint p))))))
    (fromPoint
       (groupMul_signedWindows Jacobian.add zero_point Jacobian.double
          wsize
          (fun x : Z =>
           if (x <? 0)%Z
           then
            Jacobian.opp
              (List.nth
                 (BinInt.Z.to_nat (BinInt.Z.shiftr (BinInt.Z.abs x) 1))
                 (preCompTable Jacobian.add zero_point Jacobian.double
                    wsize p) zero_point)
           else
            List.nth
              (BinInt.Z.to_nat (BinInt.Z.shiftr (BinInt.Z.abs x) 1))
              (preCompTable Jacobian.add zero_point Jacobian.double
                 wsize p) zero_point)
          (recode_rwnaf wsize (S (S (S numWindows)))
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
                    wsize numWindows n)
      (recode_rwnaf wsize
                 (S (S (S numWindows)))
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
    apply Z.ltb_lt in H1.
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
                             (S (S (S numWindows)))
                             (BinInt.Z.of_nat (bvToNat 384 n)))))
                 1))
           (preCompTable Jacobian.add zero_point
              Jacobian.double wsize p) zero_point)
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
                          (S (S (S numWindows)))
                          (BinInt.Z.of_nat (bvToNat 384 n)))))
              1))
        (preCompTable Jacobian.add zero_point Jacobian.double
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
    rewrite (@bvToNat_Z_to_nat_equiv _ _ (Z.div2 (List.nth (S (S numWindows))
              (recode_rwnaf wsize (S (S (S numWindows))) (BinInt.Z.of_nat (bvToNat 384 n))) 0%Z))).
    rewrite tableSize_correct.
    unfold tableSize.
    rewrite shiftl_to_nat_eq.
    apply Znat.Z2Nat.inj_lt.
    apply Z.div2_nonneg.
    replace (S (S numWindows)) with (Nat.pred (List.length (recode_rwnaf wsize (S (S (S numWindows))) (BinInt.Z.of_nat (bvToNat 384%nat n))) )) at 1.
    rewrite <- last_nth_equiv.
    rewrite <- hd_rev_eq_last.
    apply Z.ltb_ge; eauto.
    rewrite recode_rwnaf_length.
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
    replace (S (S numWindows)) with (Nat.pred (List.length (recode_rwnaf wsize (S (S (S numWindows))) (BinInt.Z.of_nat (bvToNat 384%nat n))) )) at 1.
    rewrite <- last_nth_equiv.
    rewrite <- hd_rev_eq_last.
    apply Z.ltb_ge; eauto.
    rewrite recode_rwnaf_length.
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
    replace (List.nth (Nat.pred (S (S (S numWindows))))
   (recode_rwnaf wsize (S (S (S numWindows)))
      (BinInt.Z.of_nat (bvToNat 384%nat n))) 0)%Z
    with
    (List.last
   (recode_rwnaf wsize (S (S (S numWindows)))
      (BinInt.Z.of_nat (bvToNat 384%nat n))) 0)%Z.
    apply recode_rwnaf_last_nonneg.
    lia.
    lia.
    trivial.
    apply last_nth_equiv_gen.
    rewrite recode_rwnaf_length.
    trivial.
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

    rewrite hd_rev_eq_last.
    apply recode_rwnaf_last_nonneg.
    lia.
    lia.
    trivial.
    (* table is not huge *)
    erewrite <- Forall2_length_eq; [ idtac | eapply preCompTable_equiv].
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
    lia.
    rewrite <- bvToNat_toZ_equiv.
    rewrite <- Z.shiftl_1_l.
    lia.
  
    intros.
    assert (b0 = c).
    eapply H2.
    subst.
    rewrite H1.
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
    lia.
    rewrite <- Z.shiftl_1_l.
    rewrite <- bvToNat_toZ_equiv.
    lia.
 
    intros.  
    destruct wsize.
    trivial.
    lia.
    apply mul_body_equiv; trivial.
    lia.
    subst.
    eapply (@recode_rwnaf_bound_In (S wsize) (S (S (S numWindows)))); try lia.
    eauto.
    apply in_rev.
    apply In_tl.
    eauto.
    rewrite rev_length.
    rewrite recode_rwnaf_length.
    lia.
    lia.

  Qed.


  Theorem point_mul_abstract_signedRegular_equiv : forall wsize numWindows n p,
    1 < wsize < 16 ->
    (BinInt.Z.of_nat (bvToNat 384%nat n) <
 BinInt.Z.shiftl 1 (BinInt.Z.of_nat (S (S (S numWindows)) * wsize)))%Z->
    jac_eq
    (fromPoint
       (groupMul_signedRegular_table Jacobian.add zero_point
          Jacobian.double Jacobian.opp wsize (S (S (S numWindows))) p
          (bvToNat _ n)))
    (seqToProd
       (point_mul_abstract wsize numWindows (Nat.pred (Nat.pred (tableSize wsize))) (prodToSeq (fromPoint p))
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

  (**
  The main result shows that the point multiplication spec extracted from Cryptol is equivalent to the basic group
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

    specialize (@groupMul_signedRegular_table_correct point jac_eq_setoid Jacobian.add Jacobian.Proper_add jac_add_assoc).
    intros.  
    rewrite H.
    reflexivity.

    apply jac_add_comm.
    apply jac_add_id_l.
    apply Jacobian.Proper_double.
    apply jac_double_correct.
    apply Proper_opp.
    apply jac_opp_correct.
    apply jac_opp_add_distr.
    apply jac_opp_involutive.
    lia.
    lia.

    eapply Z.lt_le_trans.
    apply bvToNat_lt_word.
    rewrite Z.shiftl_1_l.
    eapply Z.pow_le_mono_r.
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

  (* If we want to prove that the generic multiplication operation is correct, we need a group on generic points. *)

  Variable felem_from_bytes: (seq 384 bool -> seq 6 (seq 64 bool)) .
  Variable felem_to_bytes: seq 6 (seq 64 bool) -> seq 384 bool.

  Hypothesis felem_from_bytes_felem_to_bytes_inv : 
    forall f,
      felem_from_bytes (felem_to_bytes f) = f.
  
  Definition GenericPoint := (seq 384 Bool * (seq 384 Bool * seq 384 Bool))%type.
  Definition genericToFelems (p : GenericPoint) :=
    let '(x, (y, z)) := p in 
    (felem_from_bytes x, felem_from_bytes y, felem_from_bytes z).

  Definition generic_is_jacobian(p : GenericPoint) :=
    is_jacobian (genericToFelems p).

  Definition GenericJacobianPoint := {p : GenericPoint | generic_is_jacobian p}.

  Theorem generic_is_jac_impl_is_jac : forall (p : GenericPoint),
    generic_is_jacobian p ->
    is_jacobian (genericToFelems p).

    intros.
    unfold generic_is_jacobian in *.
    trivial.

  Qed.

  Definition genericToPoint (p : GenericPoint)(p1 : generic_is_jacobian p) : point :=
    toPoint (genericToFelems p) (generic_is_jac_impl_is_jac p p1).

  Definition genericJacobianToPoint(p : GenericJacobianPoint) : point :=
    genericToPoint (proj1_sig p) (proj2_sig p).

   Definition felemsToGeneric (p : F * F * F) : GenericPoint :=
    let '(x, y, z) := p in 
    (felem_to_bytes x, (felem_to_bytes y, felem_to_bytes z)).

  Definition pointToGeneric (p : point) : GenericPoint :=
    felemsToGeneric (fromPoint p).

  Theorem genericToFelems_felemsToGeneric_inv : forall p,
    (genericToFelems (felemsToGeneric p)) = p.

    intros.
    unfold genericToFelems, felemsToGeneric.
    destruct p.
    destruct p.
    repeat rewrite felem_from_bytes_felem_to_bytes_inv.
    reflexivity.

  Qed.

  Theorem pointToGeneric_is_jac: forall (p : point),
    generic_is_jacobian (pointToGeneric p).

    intros.
    unfold generic_is_jacobian, pointToGeneric.
    rewrite genericToFelems_felemsToGeneric_inv.
    apply fromPoint_is_jacobian.
  Qed.

  Definition pointToGenericJacobian(p : point) : GenericJacobianPoint :=
   exist _ (pointToGeneric p) (pointToGeneric_is_jac p).


  (* Correct addition on points in other formats follows from the correctness of addition in the internal format (Jacobian with saturated 64-bit limbs)
  and from the correctness of the conversion routines. As an example, the proof below shows the correctness of addition on Jacobian points
  using a generic representation (i.e. byte array) *)

  Definition jac_add_generic (p1 p2 : GenericJacobianPoint) := 
    pointToGenericJacobian (Jacobian.add (genericJacobianToPoint p1) (genericJacobianToPoint p2)).

  Definition zero_point_generic := (pointToGenericJacobian zero_point).

  Definition groupMul_generic := @GroupMulWNAF.groupMul GenericJacobianPoint jac_add_generic zero_point_generic.
  Definition point_mul_generic := point_mul_generic Fsquare Fmul Fsub Fadd Fopp felem_from_bytes felem_to_bytes.

  Local Opaque jac_eq.

  Theorem add_jac_eq_compat_r : forall p1 p2 p2',
    jac_eq (fromPoint p2) (fromPoint p2') ->
    jac_eq (fromPoint (Jacobian.add p1 p2)) (fromPoint (Jacobian.add p1 p2')).

    intros.
    eapply jacobian_eq_jac_eq.
    eapply Jacobian.Proper_add.
    reflexivity.
    eapply jac_eq_jacobian_eq.
    trivial.

  Qed.

  Theorem groupMul_generic_eq_groupMul : forall x p,
      jac_eq (fromPoint (groupMul x (genericJacobianToPoint p))) (fromPoint (genericJacobianToPoint (groupMul_generic x p))).

      induction x; intros.
      simpl in *.
      repeat rewrite felem_from_bytes_felem_to_bytes_inv.
      eapply jac_eq_refl.

      simpl.
      eapply jac_eq_trans.
      eapply add_jac_eq_compat_r.
      eapply IHx.
      simpl.
      unfold pointToGeneric.
      rewrite genericToFelems_felemsToGeneric_inv.
      eapply jac_eq_refl.

  Qed.


  Theorem point_mul_generic_correct : forall (p : GenericJacobianPoint) (n : seq 384 Bool),
      jac_eq (fromPoint (genericJacobianToPoint (groupMul_generic (bvToNat _ n) p)))
      (genericToFelems (point_mul_generic (proj1_sig p) n)).

      intros.
      unfold point_mul_generic, EC_P384_5.point_mul_generic.
      simpl.
      repeat rewrite felem_from_bytes_felem_to_bytes_inv.
      match goal with
      | [|- jac_eq _ ?x ] => rewrite <- (seqToProd_inv x)
      end.
      unfold prodToSeq.
      simpl.
      rewrite sawAt_3_equiv.
      specialize (groupMul_generic_eq_groupMul (bvToNat 384 n) p); intros.
      apply jac_eq_symm in H.
      eapply jac_eq_trans.
      apply H.
      eapply jac_eq_trans.
      apply point_mul_correct.
      unfold genericJacobianToPoint, genericToPoint.
      rewrite <- fromPoint_toPoint_id.
      unfold genericToFelems.
      generalize (proj1_sig p); intros.
      destruct g.
      destruct p0.
      unfold prodToSeq.
      unfold point_mul.
      unfold fst, snd.
      unfold F.
      eapply jac_eq_refl_abstract.
      reflexivity.
  Qed.


End ECEqProof.

