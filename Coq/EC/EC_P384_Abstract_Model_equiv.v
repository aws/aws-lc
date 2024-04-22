(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0 *)

(* Equivalence of abstract algorithmic specification and the model in GroupMulWNAF.  *)

From Coq Require Import Lists.List.
From Coq Require Import String.
From Coq Require Import Vectors.Vector.
From Coq Require Import BinPos.
From Coq Require Import Ring.
From Coq Require Import Setoid.
From Coq Require Import ZArith.BinInt.
From Coq Require Import Classes.SetoidClass.
From Coq Require Import Lia.
From Coq Require Import ZArith.Znat.
Import ListNotations.

From Crypto Require Import Algebra.Hierarchy.
From Crypto Require Import Algebra.Field.
From Crypto Require Import Algebra.Nsatz.
From Crypto Require Import Curves.Weierstrass.Jacobian.
From Crypto Require Import Curves.Weierstrass.Affine.
From Crypto Require Import Curves.Weierstrass.AffineProofs.

From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCorePrelude.
Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCorePreludeExtra.
From CryptolToCoq Require Import SAWCoreBitvectors.

From EC Require Import Util.
From EC Require Import Curve.
From EC Require Import GroupMulWNAF.
From EC Require Import EC_P384_Abstract.
From EC Require Import CryptolToCoq_equiv.
From EC Require Import WindowedMulMachine.
From EC Require Import GeneratorMul.


Local Open Scope nat_scope.

Section EC_P384_Abstract_Model_equiv.

  Definition F := Vec 6 (Vec 64 Bool).
  Definition Feq := (@eq F).
  Definition Fzero : F := (replicate 6 _ (replicate 64 _ false)).

  Instance Feq_dec : DecidableRel Feq.

    unfold Decidable.
    intros.
    apply Vector_eq_dec.
    intros.
    apply Vector_eq_dec.
    intros.
    decide equality.
  Defined.

  Context `{curve : Curve F Feq Fzero}.

  Local Notation "0" := Fzero.  Local Notation "1" := Fone.
  Local Infix "+" := Fadd. Local Infix "-" := Fsub.
  Local Infix "*" := Fmul. Local Infix "/" := Fdiv.
  Local Notation "x ^ 2" := (x*x) (at level 30).
  Local Notation "x ^ 3" := (x^2*x) (at level 30).

  Local Opaque sbvToInt.

  (* This file (like EC_P384_Abstract.v) treats several functions as abstract, even though we have concrete specifications
  for them in the implementation. This is done to simplify this part of the proof, and to make it more general. *)

  (* point doubling and addition *)
  Variable point_double : point -> point.
  Variable point_add : bool -> point -> point -> point.
  Hypothesis point_add_jac_eq : forall (a b: Curve.point) a' b',
    jac_eq (fromPoint a) (seqToProd a') ->
    jac_eq (fromPoint b) (seqToProd b') -> 
    jac_eq (fromPoint (Curve.add a b)) (seqToProd (point_add false a' b')).

  Hypothesis point_add_mixed_eq : forall (a b:Curve.point) a' b',
    nth_order b' two_lt_three = Fone -> 
    jac_eq (fromPoint a) (seqToProd a') ->
    jac_eq (fromPoint b) (seqToProd b') -> 
    jac_eq (fromPoint (Curve.add a b)) (seqToProd (point_add true a' b')).

  Hypothesis point_double_minus_3_jac_eq : forall (p:Curve.point) p',
    jac_eq (fromPoint p) (seqToProd p') ->
    jac_eq (fromPoint (Curve.double_minus_3 p)) (seqToProd (point_double p')).


  (* sign extend a 16-bit numerica value to produce a 64-bit numeric value *)
  Variable sign_extend_16_64 : (bitvector 16) -> (bitvector 64).
  Hypothesis sbvToInt_sign_extend_16_64_equiv : forall x,
    sbvToInt _ (sign_extend_16_64 x) = sbvToInt _ x.

  (* convert a 16-bit numeric value (used to identify points in a table) to a 64-bit numeric value. *)
  Variable point_id_to_limb : (bitvector 16) -> (bitvector 64).

  (* select one of two points based on whether a numeric value is nonzero *)
  Variable F_cmovznz : (bitvector 64) -> F -> F -> F.
  Hypothesis F_cmovznz_equiv : forall x y z,
    F_cmovznz x y z = if (bvEq _ x (intToBv 64 0)) then y else z.

  (* the body of a (constant time) lookup into a table of Jacobian points that returns one of two points depending
  on whether two numeric values are equal *)
  Variable select_point_loop_body : (bitvector 64) -> point -> (bitvector 64) -> point -> point.
  Hypothesis select_point_loop_body_equiv : forall w x y z,
    select_point_loop_body w x y z = 
       if (bvEq _ y w) then z else x.

  (* the body of a (constant time) lookup into a table of affine points that returns one of two points depending
  on whether two numeric values are equal *)
  Variable select_point_affine_loop_body : (bitvector 64) -> affine_point -> (bitvector 64) -> affine_point -> affine_point.
  Hypothesis select_point_affine_loop_body_equiv : forall w x y z,
    select_point_affine_loop_body w x y z = 
       if (bvEq _ y w) then z else x.

  (* subtract one point from another only when a numeric value is even *)
  Variable conditional_subtract_if_even: point -> bitvector 384 -> point -> point.
  Definition point_opp_abstract := @point_opp_abstract Fopp.
  Hypothesis conditional_subtract_if_even_jac_eq_ite : forall n p1 p2,
    jac_eq (seqToProd (conditional_subtract_if_even p1 n p2)) (seqToProd (if (Nat.even (bvToNat _ n)) then (point_add false p1 (point_opp_abstract p2)) else p1)).


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

    econstructor.
    eauto.

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


  Definition double_add_body_abstract := @double_add_body_abstract Fopp F_cmovznz select_point_loop_body 
    point_add point_double sign_extend_16_64.
  Definition select_point_abstract := @select_point_abstract select_point_loop_body.

  Theorem select_point_abstract_nth_equiv_h : forall ls n a,
    (Z.of_nat (List.length ls) < 2^64 )%Z ->
     (Z.of_nat n < 2^64 )%Z ->
    List.fold_left
      (fun (acc : Vec 3 (Vec 6 (Vec 64 bool)))
         (p : Vec 64 bool * Vec 3 (Vec 6 (Vec 64 bool))) =>
       select_point_loop_body (bvNat 64 (a + n)%nat) acc (fst p) (snd p))
      (combine (List.map (bvAdd _ (bvNat _ a)) (toN_excl_bv 64 (Datatypes.length ls))) ls)
      (of_list [Fzero; Fzero; Fzero]) =
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

  Theorem map_bvAdd_0 : forall n ls,
    (List.map (bvAdd n (bvNat n 0%nat)) ls) = ls.

    induction ls; intros; simpl in *.
    reflexivity.
    rewrite IHls.
    f_equal.
    apply bvAdd_id_l.

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
    Jacobian.eq (groupDouble_n n zero_point) zero_point.

    intros.
    apply (@groupDouble_n_id _ _ EC_CommutativeGroup EC_CommutativeGroupWithDouble).

  Qed.
  
  Definition pre_comp_table_abstract := @pre_comp_table_abstract point_add point_double.

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

  Theorem preCompTable_equiv_h : forall ls1 ls2 p1 p2,
    List.length ls1 = List.length ls2 ->
    jac_eq (fromPoint p1) (seqToProd p2) ->
    List.Forall2
  (fun (a0 : Curve.point) (b0 : Vec 3 F) =>
   jac_eq (fromPoint a0) (seqToProd b0))
  (CryptolToCoq_equiv.scanl
     (fun (a0 : Jacobian.point) (_ : nat) =>
      Jacobian.add (Jacobian.double p1) a0)
     ls1 p1)
  (CryptolToCoq_equiv.scanl
     (fun (z : Vec 3 (Vec 6 (Vec 64 Bool)))
        (_ : Integer) =>
      point_add false
        (point_double
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
    eapply jac_eq_trans; [idtac | apply point_double_minus_3_jac_eq].
    apply Jacobian.double_minus_3_eq_double.
    rewrite seqToProd_inv in H0.
    rewrite seqToProd_inv.
    eauto.
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

  Local Opaque fromPoint.

  Theorem groupDouble_n_fold_left_double_equiv : forall (A : Type) ws ls a1 a2,
    List.length ls = ws ->
    jac_eq (fromPoint a1) (seqToProd a2) ->
    jac_eq 
  (fromPoint (groupDouble_n ws a1))
  (seqToProd
     (List.fold_left
        (fun (x : Vec 3 (Vec 6 (Vec 64 bool))) (_ : A)
         =>
         point_double x) ls a2)).

    induction ws; destruct ls; intros; simpl in *; try lia.
    trivial.
    eapply jac_eq_trans; [idtac | eapply IHws].
    apply jacobian_eq_jac_eq.
    eapply (@groupDouble_n_double_comm_jac _ _ EC_CommutativeGroup EC_CommutativeGroupWithDouble).
    lia.
    assert (exists a2', (seqToProd a2) = (fromPoint a2')).
    eapply jac_eq_point_ex; eauto.
    destruct H1. subst.
    replace a2 with (prodToSeq (fromPoint x)).
    eapply jac_eq_trans; [idtac | apply point_double_minus_3_jac_eq].
    apply jacobian_eq_jac_eq.
    eapply Jacobian.double_minus_3_eq_double.
    rewrite seqToProd_inv.

    rewrite <- H1.
    trivial.
    rewrite <- H1.
    apply prodToSeq_inv.
 
  Qed.

  Definition conditional_point_opp_abstract := @conditional_point_opp_abstract Fopp.

  Theorem point_opp_equiv : forall p,
    jac_eq 
    (fromPoint (Jacobian.opp p))
    (seqToProd (point_opp_abstract (prodToSeq (fromPoint p)))).

    intros.
    unfold point_opp_abstract, EC_P384_Abstract.point_opp_abstract. simpl.
    unfold seqToProd, prodToSeq, nth_order. simpl.
    destruct p. simpl.
    destruct x. simpl.
    destruct p. 
    apply jac_eq_refl.
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
    (seqToProd (point_opp_abstract (prodToSeq p))) = point_opp_prod p.

    intros.
    reflexivity.

  Qed.


  Theorem conditional_point_opp_equiv : forall x p1 p2,
    jac_eq (fromPoint p1) (seqToProd p2) ->
    jac_eq
  (seqToProd
     (conditional_point_opp_abstract F_cmovznz x p2))
  (fromPoint (if (dec ((sbvToInt _ x) = 0%Z)) then p1 else (Jacobian.opp p1))).

    intros.
    unfold conditional_point_opp_abstract, EC_P384_Abstract.conditional_point_opp_abstract.
    rewrite F_cmovznz_equiv.
    destruct (dec (sbvToInt 64 x = 0%Z)); intros.
    apply sbvToInt_0_replicate in e.
    subst.
    rewrite rep_false_eq_int_bv.
    rewrite bvEq_refl.
    rewrite nth_order_3_equiv.
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
    unfold seqToProd, point_opp_abstract; simpl.
    
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

  Qed.

  Theorem conditional_point_opp_ifso_equiv : forall x p1 p2,
    sbvToInt _ x <> 0%Z ->
    jac_eq (fromPoint p1) (seqToProd p2) ->
    jac_eq
  (seqToProd
     (conditional_point_opp_abstract F_cmovznz x p2))
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
     (conditional_point_opp_abstract F_cmovznz x p2))
  (fromPoint p1).

    intros.
    eapply jac_eq_trans.
    eapply conditional_point_opp_equiv; eauto.
    destruct (dec (sbvToInt 64 x = 0%Z)).
    apply jac_eq_refl.
    congruence.

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
              opp
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
         (double_add_body_abstract pred_wsize
            (EC_P384_Abstract.pre_comp_table_abstract point_add point_double (Nat.pred (Nat.pred (tableSize (S pred_wsize))))
               (prodToSeq (fromPoint p))) a2 b2)).

    intros.
    unfold double_add_body_abstract, EC_P384_Abstract.double_add_body_abstract.

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
    unfold point_id_to_limb_abstract.
    
    assert (63 < 64)%nat by lia.
    eapply (sbvToInt_nz_nth _ H1).
    assert (15 < 16) by lia.
    erewrite (@nth_order_Vec_append_eq Bool _ 16 _ 48 (intToBv 48 0) 15 H1 H4).
    simpl. 
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
    rewrite sbvToInt_sign_extend_16_64_equiv.
    reflexivity.

    eapply Z.le_lt_trans.
    apply (@Z.opp_le_mono (2 ^ Z.of_nat (S pred_wsize))).
    apply Z.pow_le_mono.
    lia.
    lia.
    rewrite sbvToInt_sign_extend_16_64_equiv.
    lia.

    rewrite (@bvToNat_Z_to_nat_equiv _ _ (Z.div2 (Z.abs (sbvToInt _ b2)))).
    rewrite Z.div2_spec.
    reflexivity.
    apply Z.div2_nonneg.
    lia.

    rewrite sbvToInt_sign_extend_16_64_equiv.
    erewrite bvSShr_Z_shiftr_equiv; [idtac | idtac | erewrite ct_abs_equiv]; eauto.
    rewrite Z.div2_spec.
    rewrite sbvToInt_sign_extend_16_64_equiv.
    reflexivity.

    eapply Z.le_lt_trans.
    apply (@Z.opp_le_mono (2 ^ Z.of_nat (S pred_wsize))).
    apply Z.pow_le_mono.
    lia.
    lia.
    rewrite sbvToInt_sign_extend_16_64_equiv.
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
    unfold point_id_to_limb_abstract.
    
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
    rewrite sbvToInt_sign_extend_16_64_equiv.
    reflexivity.

    eapply Z.le_lt_trans.
    apply (@Z.opp_le_mono (2 ^ Z.of_nat (S pred_wsize))).
    apply Z.pow_le_mono.
    lia.
    lia.
    rewrite sbvToInt_sign_extend_16_64_equiv.
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

  Theorem pre_comp_table_abstract_nth_0  : forall wsize p def,
    List.nth 0 (pre_comp_table_abstract (Nat.pred (Nat.pred (tableSize wsize)))
              p) def = p.
  
    intros.
    unfold pre_comp_table_abstract, EC_P384_Abstract.pre_comp_table_abstract.
    rewrite nth_0_hd_equiv.
    apply scanl_head.

  Qed.

  
  (* test for whether a field element is nonzero and return the result as a numeric value *)
  Variable F_nz : F -> bitvector 64.  

  Hypothesis F_nz_0 : forall x, 
    F_nz x = intToBv 64 0 ->
    x = 0.
  
  Hypothesis F_nz_not_0 : forall x, 
    ~(F_nz x = intToBv 64 0) ->
    x <> 0.

  Theorem F_nz_eq_0 : 
    (F_nz 0) = (intToBv 64 0).

    intros.
    destruct (bvector_eq_dec (F_nz 0) (intToBv 64 0)).
    trivial.
    exfalso.
    eapply (F_nz_not_0).
    eauto.
    trivial.

  Qed.

  Theorem F_nz_neq_0 : forall x,
    x <> 0 ->
   (F_nz x) <> (intToBv 64 0).

    intros.
    destruct (bvector_eq_dec (F_nz x) (intToBv 64 0)); trivial.
    exfalso.
    apply H.
    apply F_nz_0.
    trivial.
  Qed.

  Definition F_ne := @F_ne Fsub F_nz.

  Theorem F_ne_0 : forall a b, 
    F_ne a b = intToBv 64 0 ->
    a = b.

    intros.
    unfold F_ne, EC_P384_Abstract.F_ne in *.
    destruct (dec (Feq (a0 - b0) 0)).
    eapply Fsub_0_eq.
    trivial.

    exfalso.
    eapply F_nz_neq_0.
    intuition idtac.
    eapply n.
    eapply H0.
    trivial.

  Qed.

  Theorem F_ne_not_0 : forall a b, 
    F_ne a b <> intToBv 64 0 ->
    a <> b.

    intros.
    eapply F_nz_not_0 in H.
    
    eapply Fsub_not_0_neq.
    eapply H.
    
  Qed.

  Definition jacobian_affine_eq_abstract := @jacobian_affine_eq_abstract Fone Fadd Fsub Fmul Fdiv Fopp Finv _ a b _ F_nz.

  Theorem jacobian_affine_eq_abstract_jac_eq_equiv : forall s p a,
    jac_eq (seqToProd s) (fromPoint p) ->
    jacobian_affine_eq_abstract s a =
    jacobian_affine_eq_abstract (prodToSeq (fromPoint p)) a.

    intros.
    unfold jacobian_affine_eq_abstract, EC_P384_Abstract.jacobian_affine_eq_abstract, jac_eq in *.
    simpl in *.
    remember (fromPoint p) as z.
    destruct z.
    destruct p0.
    destruct (Vec_S_cons _ _ s).
    destruct H0.
    subst.
    destruct (Vec_S_cons _ _ x0).
    destruct H0.
    subst.
    destruct (Vec_S_cons _ _ x2).
    destruct H0.
    subst.
    rewrite (@Vec_0_nil _ x3) in *.
    simpl in *.
    unfold nth_order in *.  
    simpl in *.
    generalize (nth a0 (Fin.FS Fin.F1)); intros.
    generalize (nth a0 Fin.F1); intros.
    destruct (dec (Feq x0 0)); 
    repeat match goal with
    | [|- context[ bvEq ?a ?b ?c]] => case_eq (bvEq a b c); intros
    | [H: bvEq ?a ?b ?c = true |- _] => apply bvEq_eq in H
    | [H: bvEq ?a ?b ?c = false |- _] => apply bvEq_neq in H
    | [H: EC_P384_Abstract.F_ne _ ?a ?b = intToBv 64 0 |- _ ] => apply F_ne_0 in H
    | [H: EC_P384_Abstract.F_ne _ ?a ?b <> intToBv 64 0 |- _ ] => apply F_ne_not_0 in H
    | [H: F_nz ?x = intToBv 64 0 |- _] => eapply F_nz_0 in H
    | [H: F_nz ?x <> intToBv 64 0 |- _] => eapply F_nz_not_0 in H
    end; trivial; simpl in *; unfold Feq in *; subst; exfalso;
    repeat match goal with
    | [H: F_nz 0 <> intToBv 64 0 |- _ ] => eapply H; reflexivity
    | [H: F_nz ?x = intToBv 64 0 |- _] => eapply F_nz_0 in H
    | [H: F_nz ?x = intToBv 64 0 -> False |- _] => eapply F_nz_not_0 in H
    end; intuition idtac.

    setoid_replace (f2 * (@Fsquare Fmul x0 * x0) * f ^ 3) with (f2 * f ^ 3 * (@Fsquare Fmul x0 * x0) )in H4.
    apply fmul_same_r_if in H4.
    unfold Feq in *.
    subst.
    intuition idtac.
    eapply mul_nz.
    eapply mul_nz.
    intuition idtac;
    eauto.
    intuition idtac;
    eauto.
    intuition idtac;
    eauto.
    nsatz.
    
    setoid_replace (f3 * @Fsquare Fmul x0 * f ^ 2) with (f3 * f ^ 2 * @Fsquare Fmul x0) in H.
    apply fmul_same_r_if in H.
    unfold Feq in *.
    subst.
    intuition idtac.
    eapply mul_nz.
    intuition idtac;
    eauto.
    intuition idtac;
    eauto.
    nsatz.

    setoid_replace (f3 * @Fsquare Fmul x0 * f ^ 2) with (f3 * f ^ 2 * @Fsquare Fmul x0) in H.
    apply fmul_same_r_if in H.
    unfold Feq in *.
    subst.
    intuition idtac.
    eapply mul_nz.
    intuition idtac;
    eauto.
    intuition idtac;
    eauto.
    nsatz.

    replace (f2 * (@Fsquare Fmul f * f) * x0 ^ 3) with (f2 * x0 ^ 3 * (@Fsquare Fmul f * f)) in H5.
    apply fmul_same_r_if in H5.
    unfold Feq in *.
    subst.
    intuition idtac.
    eapply mul_nz.
    unfold Fsquare.
    eapply mul_nz.
    intuition idtac;
    eauto.
    intuition idtac;
    eauto.
    intuition idtac;
    eauto.
    nsatz.

    replace (f3 * @Fsquare Fmul f * x0 ^ 2) with (f3 * x0 ^ 2 * @Fsquare Fmul f) in H.
    apply fmul_same_r_if in H.
    unfold Feq in *.
    subst.
    intuition idtac.
    unfold Fsquare.
    eapply mul_nz.
    intuition idtac;
    eauto.
    intuition idtac;
    eauto.
    nsatz.

    replace (f3 * @Fsquare Fmul f * x0 ^ 2) with (f3 * x0 ^ 2 * @Fsquare Fmul f) in H.
    apply fmul_same_r_if in H.
    unfold Feq in *.
    subst.
    intuition idtac.
    unfold Fsquare.
    eapply mul_nz.
    intuition idtac;
    eauto.
    intuition idtac;
    eauto.
    nsatz.

  Qed.

  Theorem toN_excl_add_natsFrom_equiv : forall y x,
    List.Forall2 (fun (x0 : Z) (y0 : nat) => (Z.of_nat x + x0)%Z = Z.of_nat y0)
    (toN_excl_int y) (natsFrom x y).

    induction y; intros.
    simpl in *.
    econstructor.
    erewrite natsFrom_S.
    simpl in *.
    eapply Forall2_app.
    eapply IHy.
    econstructor.
    lia.
    econstructor.  
    eauto.
  Qed.

  Theorem toN_add_natsFrom_equiv : forall x y,
    List.Forall2 (fun x y => x = Z.of_nat y)
      (List.map (BinInt.Z.add (Z.of_nat x)) (toN_int y))
      (natsFrom x (S y)).

    intros.
    unfold toN_int.
    erewrite natsFrom_S; eauto.
    eapply Forall2_map_l.
    eapply Forall2_app.
    eapply toN_excl_add_natsFrom_equiv.
    econstructor.
    lia.
    econstructor.
    
  Qed.

  Theorem toN_bv_length : forall x n,
    List.length (toN_bv x n) = S n.

    intros.
    unfold toN_bv.
    rewrite app_length.
    rewrite toN_excl_bv_length.
    simpl. lia.
  
  Qed.

  (* Definitions and facts that depend on window size *)
  Section EC_P384_Abstract_Model_equiv_wsize.

    (* Window size and number of windows *)
    Variable wsize : nat.
    Hypothesis wsize_range : (1 < wsize < 16)%nat.
    Variable nw : nat.
    Hypothesis nw_range : nw <> 0%nat.

    Definition numPrecompExponentGroups : nat := (Nat.pred wsize).

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
    
    Theorem point_mul_abstract_signedRegular_cases : forall n p,
      (BinInt.Z.of_nat (bvToNat 384%nat n) <
     BinInt.Z.shiftl 1 (BinInt.Z.of_nat (S (S (S nw)) * wsize)))%Z->
        jac_eq
      (seqToProd
         (List.fold_left
            (double_add_body_abstract (Nat.pred wsize)
               (EC_P384_Abstract.pre_comp_table_abstract point_add point_double (Nat.pred (Nat.pred (tableSize wsize)))
                  (prodToSeq (fromPoint p))))
            (skipn 1
               (List.rev (mul_scalar_rwnaf_abstract wsize nw n)))
            (select_point_abstract
               (sign_extend_16_64
                  (bvSShr 15
                     (List.nth (S (S nw))
                        (mul_scalar_rwnaf_abstract wsize nw n)
                        (bvNat 16 0%nat)) 1))
               (EC_P384_Abstract.pre_comp_table_abstract point_add point_double (Nat.pred (Nat.pred (tableSize wsize)))
                  (prodToSeq (fromPoint p))))))
      (fromPoint
         (groupMul_signedWindows
            wsize
            (fun x : Z =>
             if (x <? 0)%Z
             then
              opp
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

      eapply (jac_eq_trans _
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
        (add
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
      unfold idElem. simpl.
      apply groupDouble_n_zero.
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
      split.
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
      destruct (dec (wsize = 0%nat)).
      subst.
      lia.

      replace wsize with (S (pred wsize)).
      apply mul_body_equiv; trivial.
      destruct wsize; simpl; lia.
      subst.
      eapply (@recode_rwnaf_bound_In (S (pred wsize)) _ (S (S (S nw)))); try lia.
      destruct wsize; simpl in *; try lia; eauto.
      apply in_rev.
      apply In_tl.
      destruct wsize; simpl in *; try lia; eauto.
      destruct wsize; simpl in *; lia.
      rewrite rev_length.
      rewrite recode_rwnaf_length.
      lia.
      lia.
      lia.

      Unshelve.
      lia.

    Qed.


    Definition point_mul_abstract := @point_mul_abstract Fopp F_cmovznz select_point_loop_body point_add point_double sign_extend_16_64 conditional_subtract_if_even.

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
      unfold point_mul_abstract, EC_P384_Abstract.point_mul_abstract.
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
      unfold double_add_body_abstract.

      trivial.
      trivial.

      rewrite pre_comp_table_abstract_nth_0.
      apply jac_eq_refl_abstract.
      unfold point_opp_abstract, prodToSeq, seqToProd.
      simpl.
      destruct p. simpl. destruct x. destruct p. simpl.
      unfold nth_order. simpl.
      reflexivity.

      apply point_mul_abstract_signedRegular_cases; trivial.

    Qed.

    Theorem point_mul_abstract_correct : forall (p : Curve.point) (n : Vec 384 bool),
        (384 <= (S (S (S nw))) * wsize)%nat -> 
        jac_eq (fromPoint (groupMul (bvToNat _ n) p))
        (seqToProd (point_mul_abstract wsize nw (Nat.pred (Nat.pred (tableSize wsize))) (prodToSeq (fromPoint p)) n)).

      intros.
      eapply jac_eq_trans; [idtac | eapply point_mul_abstract_signedRegular_equiv]; eauto.
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

      eapply Z.lt_le_trans.
      apply bvToNat_lt_word.
      rewrite Z.shiftl_1_l.
      eapply Z.pow_le_mono_r.
      lia.
      lia.

    Qed.

    (* The base point and precomputed table of multiples of the base point *)
    Variable g : Curve.point.
    Variable  base_precomp_table : list (list affine_point).
    Definition affine_g : affine_point := affine_g base_precomp_table.
    (* We need a default point for some lookup operations. It simplifies the proof a bit if this point is on the curve. *)
    Definition affine_default : affine_point := affine_g.
    Definition affineToJac := @affineToJac Fone Fadd Fsub Fmul Fdiv Fopp Finv _ a b _.
    (* Assume that the Jacobian base point is equivalent to the first point in the table *)
    Hypothesis g_affine_jac_equiv :   
      jac_eq (seqToProd (affineToJac affine_g)) (fromPoint g).
    (* Assume that the precomputed table has the correct length, each entry in the table has the correct length, and the
    values in the table have been validated. *)
    Hypothesis base_precomp_table_length : List.length base_precomp_table = (wsize * (Nat.pred wsize))%nat.
    Hypothesis base_precomp_table_entry_length : 
      forall ls, List.In ls base_precomp_table -> List.length ls = Nat.pow 2 numPrecompExponentGroups.
    Definition validate_base_table_abstract := @validate_base_table_abstract Fone Fadd Fsub Fmul Fdiv Fopp Finv _ a b _ point_add point_double F_nz.
    Hypothesis base_precomp_table_validated : validate_base_table_abstract wsize base_precomp_table = true.

    Definition validateGeneratorTable := validateGeneratorTable g (fun p: Curve.point => jacobian_affine_eq_abstract (prodToSeq (fromPoint p))) affine_default.

    Lemma point_double_jac_eq : forall (x:Curve.point) x',
      jac_eq (fromPoint x) (seqToProd x') ->
      jac_eq (fromPoint (Curve.double x)) (seqToProd (point_double x')).

      intros.
      eapply jac_eq_trans; [idtac | apply point_double_minus_3_jac_eq].
      eapply jacobian_eq_jac_eq.
      apply double_minus_3_eq_double.
      trivial.

    Qed.

    Theorem validate_base_table_abstract_model_equiv : 
      validate_base_table_abstract wsize base_precomp_table = validateGeneratorTable base_precomp_table.

      intros.
      unfold validate_base_table_abstract, EC_P384_Abstract.validate_base_table_abstract, validateGeneratorTable, GroupMulWNAF.validateGeneratorTable.
      eapply (@fold_left_R _ _ _ _ (fun x y => jac_eq (seqToProd (fst x)) (fromPoint (fst y)) /\ snd x = snd y) eq).
      intuition idtac.

      eapply forall2_eq; eauto.

      intros.
      subst.
      unfold validate_base_table_body_abstract, EC_P384_Abstract.validate_base_row_abstract, validateGeneratorTableBody.
      Local Opaque jac_eq.
      destruct a1. destruct a2. simpl in *.
      destruct H; subst.

      split.
      eapply jac_eq_symm.
      eapply groupDouble_n_fold_left_double_equiv; eauto.
      rewrite toN_bv_length.
      symmetry.
      transitivity (wsize * (Nat.pred wsize))%nat.
      apply base_precomp_table_length.
      destruct wsize; simpl in *. lia.
      destruct n; simpl in *; lia.
      apply jac_eq_symm; eauto.
      
      destruct b1; simpl; trivial.
      unfold validate_base_row_abstract, EC_P384_Abstract.validate_base_row_abstract, validateGeneratorTableRow.
      eapply (@fold_left_R _ _ _ _ (fun x y => jac_eq (seqToProd (fst x)) (fromPoint (fst y)) /\ snd x = snd y) eq).
      unfold fst, snd.
      split.
      unfold groupAdd, groupDouble.
      simpl.
      eapply jac_eq_symm.
      eapply point_add_jac_eq.
      apply jac_eq_symm; eauto.
      eapply point_double_jac_eq.
      apply jac_eq_symm.
      eauto.

      erewrite nth_indep.
      eapply jacobian_affine_eq_abstract_jac_eq_equiv.
      eauto.
      erewrite base_precomp_table_entry_length; eauto.
      specialize (@PeanoNat.Nat.pow_nonzero 2 numPrecompExponentGroups).
      intuition idtac.
      lia.

      apply Forall2_map_l.
      apply Forall2_map_r.
      erewrite base_precomp_table_entry_length.
      unfold numPrecompExponentGroups.
      eapply Foralll2_impl.
      specialize (@toN_add_natsFrom_equiv 1%nat (Nat.pred (Nat.pred (PeanoNat.Nat.pow 2 (Nat.pred wsize))))); intros.
      replace (S (Nat.pred (Nat.pred (PeanoNat.Nat.pow 2 (Nat.pred wsize))))) with ((Nat.pred (PeanoNat.Nat.pow 2 (Nat.pred wsize)))) in *.
      eauto.
      assert (2%nat <= (PeanoNat.Nat.pow 2 (Nat.pred wsize))).
      transitivity (PeanoNat.Nat.pow 2%nat 1%nat).
      reflexivity.
      apply NPeano.Nat.pow_le_mono_r_iff.
      lia.
      lia.
      lia.

      intros.
      simpl in H4; subst.
      rewrite Znat.Nat2Z.id.
      eapply nth_indep.
      rewrite base_precomp_table_entry_length.
      unfold numPrecompExponentGroups.
      eapply In_natsFrom_range in H3; eauto.
      lia.
      eauto.
      eauto.
      
      intros.
      simpl.
      destruct H0.
      subst.
      split.  
      apply jac_eq_symm.
      apply point_add_jac_eq.
      apply jac_eq_symm; eauto.
      apply point_double_jac_eq.
      apply jac_eq_symm.
      eauto.
      f_equal.
      eauto.
      apply jacobian_affine_eq_abstract_jac_eq_equiv.
      eauto.
    Qed.

    Theorem jacobian_affine_eq_abstract_correct : 
      forall p (t : affine_point),
        jacobian_affine_eq_abstract (prodToSeq p) t = 1%bool <-> jac_eq (seqToProd (affineToJac t)) p.

      intros.
      destruct p.
      destruct p.
      destruct (Vec_S_cons _ _ t).
      destruct H.
      subst.
      destruct (Vec_S_cons _ _ x0).
      destruct H.
      subst.
      rewrite (@Vec_0_nil _ x2).
      unfold prodToSeq.
      simpl.
      Local Transparent jac_eq.
      unfold jacobian_affine_eq_abstract, EC_P384_Abstract.jacobian_affine_eq_abstract.
      simpl in *.
      unfold sawAt.
      simpl.
      unfold affineToJac.
      simpl.
      unfold nth_order.
      simpl.

      replace (f0 * 1 ^ 2) with f0.
      replace (f1 * 1 ^ 3) with f1.

      destruct (dec (Feq 1 0)); 
      repeat match goal with
      | [|- context[if ?a then _ else _]] => case_eq a; intros
      end; split; intros;
      
      repeat match goal with
      | [H : false = true |- _ ] => discriminate
      | [H : Feq 1 0 |- _] => 
            exfalso; eapply Fone_ne_Fzero; eauto
      | [H :  bvEq _ _ _  = true |- _] => apply bvEq_eq in H
      | [H :  bvEq _ _ _  = false |- _] => apply bvEq_neq in H
       | [H : EC_P384_Abstract.F_ne _ _ _ = intToBv 64 0 |- _ ] => apply F_ne_0 in H
      | [H : EC_P384_Abstract.F_ne _ _ _ <> intToBv 64 0 |- _ ] => apply F_ne_not_0 in H
      | [H : F_nz _ = intToBv 64 0 |- _ ] => apply F_nz_0 in H
      | [H : F_nz _ <> intToBv 64 0 |- _ ] => apply F_nz_not_0 in H
      | [H : negb _ = true |- _ ] => apply negb_true_false in H
      | [H : negb _ = false |- _ ] => apply negb_false_true in H
      end;
      intuition idtac.

      nsatz.
      nsatz.

    Qed.

    Definition jacobian_affine_eq_point (p : Curve.point) :=
      jacobian_affine_eq_abstract (prodToSeq (fromPoint p)).

    Theorem jacobian_affine_eq_point_correct : 
    forall (p : Curve.point) (t : affine_point),
      jacobian_affine_eq_point p t = 1%bool <-> jac_eq (seqToProd (affineToJac t)) (fromPoint p).

      intros.
      eapply jacobian_affine_eq_abstract_correct; eauto.

    Qed.

    Theorem base_precomp_table_correct  : forall n1 n2,
      (n1 <  (wsize * (Nat.pred wsize)))%nat ->
      (n2 < Nat.pow 2 numPrecompExponentGroups)%nat-> 
      jac_eq (seqToProd (affineToJac (List.nth n2 (List.nth n1 base_precomp_table List.nil) affine_default))) (fromPoint (groupMul ((2 * n2 + 1) * (Nat.pow 2 (n1 * numPrecompExponentGroups * wsize))) g)).

      intros.
      eapply validateGeneratorTable_correct.
      lia.
      intros.
      eapply jacobian_affine_eq_point_correct.
      trivial.
      intros.
      eapply jac_eq_trans; eauto.
      rewrite validate_base_table_abstract_model_equiv in base_precomp_table_validated.
      eapply base_precomp_table_validated.
      unfold validate_base_table_abstract, EC_P384_Abstract.validate_base_table_abstract in *.
      trivial.

      rewrite base_precomp_table_length.
      lia.
      trivial.
      unfold numPrecompExponentGroups.
      rewrite NPeano.Nat.mul_comm.
      rewrite base_precomp_table_length.
      reflexivity.

      apply base_precomp_table_entry_length.

    Qed.

    Definition affineOpp (x : affine_point) :=
      cons _ (nth_order x zero_lt_two) _ (cons _ (Fopp (nth_order x one_lt_two)) _ (@nil F)).

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
      rewrite (@Vec_0_nil _ x2) in *.
      simpl in *.
      destruct (dec (Feq 1 0)).
      exfalso.
      apply Fone_ne_Fzero; auto.
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
      rewrite base_precomp_table_length in H2.
      eauto.
      erewrite base_precomp_table_entry_length in H1.
      eauto.
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
      match goal with
      | [|- (0 < ?a)%nat ] => 
        replace a with (wsize * Nat.pred wsize)%nat
      end.
      destruct wsize; simpl in *; lia.
      eapply nth_In.
      match goal with
      | [|- (0 < ?a)%nat ] => 
        replace a with (wsize * Nat.pred wsize)%nat
      end.
      destruct wsize; simpl in *; lia.
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
      unfold affineToJac, EC_P384_Abstract.affineToJac, is_jacobian, on_curve in *.
      simpl.
      match goal with
      | [|- if (dec (Feq ?a _)) then _ else _ ] => replace a with Fone
      end.
      destruct (dec (Feq 1 0)).
      trivial.
      replace (b * (1 ^ 3) ^ 2) with b.

      match goal with 
      | [|- context [?a * ?b * (1^2)^2]] => replace (a * b * (1^2)^2) with (a * b)
      end.

      repeat rewrite (@nth_order_Vec_append_l_eq _ _ 1%nat _ 2%nat _ _ _ zero_lt_two); intros.
      rewrite (@nth_order_Vec_append_l_eq _ _ 1%nat _ 2%nat _ _ _ one_lt_two); intros.
      unfold Feq, EC_P384_Abstract.Feq in *.
      rewrite H.
      nsatz.

      nsatz.
      nsatz.
      symmetry.
      transitivity (nth_order (cons F 1 0 (nil F)) zero_lt_one).
      apply (@nth_order_Vec_append_eq F _ 1%nat (cons F 1 0 (nil F)) 2%nat affinePt 0%nat two_lt_three ).
      reflexivity.

    Qed.

    Theorem affineOpp_toPoint_eq :  forall p,
      jac_eq
      (seqToProd
         (affineToJac
            (affineOpp p))) 
       (seqToProd (point_opp_abstract (affineToJac p))).

      intros.
      unfold point_opp_abstract, EC_P384_Abstract.point_opp_abstract.
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

    Definition pExpMultiple (n : nat) (x : Z) : Curve.point := 
      let absPt := affinePointLookup (Z.to_nat (Z.div2 (Z.abs x))) n in
      let affinePt :=  affineOppIfNegative x absPt in
      toPoint (seqToProd (affineToJac affinePt)) (affineIsJacobian _ (affineOppIfNegative_on_curve _ _ (affinePointLookup_on_curve _ _ ))).

    Theorem OddWindow_precomp_abs_le : forall w,
        OddWindow wsize w -> 
        (Z.to_nat (Z.div2 (Z.abs w)) < Nat.pow 2 numPrecompExponentGroups)%nat.

        unfold OddWindow, GroupMulWNAF.OddWindow in *.
        intuition idtac.
        eapply PeanoNat.Nat.lt_le_trans.
        eapply Znat.Z2Nat.inj_lt.
        eapply Z.div2_nonneg.
        lia.
        assert (0 <= Z.pow 2 (Z.of_nat (Nat.pred wsize))%nat)%Z.
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
      rewrite Z.shiftl_mul_pow2 in *.
      eapply Z.lt_le_trans.
      rewrite Z.abs_eq in *.
      eauto.
      lia.
      rewrite Z.mul_1_l.
      rewrite Zpower.two_power_nat_equiv.
      replace wsize with (S (Nat.pred wsize)) at 1.
      reflexivity.
      lia.
      lia.
      rewrite Zpower.two_power_nat_equiv.
      reflexivity.
      rewrite Znat.Z2Nat.inj_pow.
      rewrite Znat.Nat2Z.id.
      reflexivity.
      lia.
      lia.

    Qed.

    Theorem point_opp_jac_eq_proper : forall p1 p2,
      jac_eq (seqToProd p1) (seqToProd p2) ->
      jac_eq 
        (seqToProd (point_opp_abstract p1))
         (seqToProd (point_opp_abstract p2)).

      intros.
      unfold point_opp_abstract, EC_P384_Abstract_Model_equiv.point_opp_abstract, EC_P384_Abstract.point_opp_abstract.
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

   
    Theorem pExpMultiple_correct : forall n w,
          (n < (wsize * (Nat.pred wsize)))%nat -> 
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
        (seqToProd (point_opp_abstract (affineToJac (affinePointLookup (Z.to_nat (Z.div2 (Z.abs w))) n))))
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
      trivial.
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
      trivial.
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

    Definition groupedMul_scalar_precomp d s :=
      match (groupedMul_precomp wsize (S (S (S nw))) g numPrecompExponentGroups pExpMultiple d (recode_rwnaf wsize (S (S (S nw))) (Z.of_nat s))) with
      | Some x => 
        if (Nat.even s) then Some (Jacobian.add x (Jacobian.opp g)) else Some x
      | None => None
      end.

    Theorem zero_point_jac_eq : 
      jac_eq (fromPoint zero_point)
       (seqToProd (replicate 3 (Vec 6 (bitvector 64)) (replicate 6 (bitvector 64) (intToBv 64 0)))).

      unfold zero_point, zero_point_h.
      Local Transparent fromPoint.
      unfold fromPoint.
      simpl.
      destruct (dec (Feq 0 0)). trivial.
      exfalso.
      intuition idtac.
      eapply n. reflexivity.
      Local Opaque fromPoint.
    Qed.

    Theorem select_point_affine_abstract_nth_equiv_h : forall ls n a,
      (Z.of_nat (List.length ls) < 2^64 )%Z ->
       (Z.of_nat n < 2^64 )%Z ->
      List.fold_left
        (fun acc p =>
         select_point_affine_loop_body (bvNat 64 (a + n)%nat) acc (fst p) (snd p))
        (combine (List.map (bvAdd _ (bvNat _ a)) (toN_excl_bv 64 (Datatypes.length ls))) ls)
        (of_list (List.cons Fzero (List.cons Fzero List.nil))) =
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

    Definition select_point_affine_abstract := @select_point_affine_abstract Fone Fadd Fsub Fmul Fdiv Fopp Finv _ a b _ select_point_affine_loop_body.

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

    Definition add_base_abstract := @add_base_abstract Fone Fadd Fsub Fmul Fdiv Fopp Finv _ a b _ F_cmovznz point_add sign_extend_16_64 base_precomp_table select_point_affine_loop_body Fone.

    Theorem add_base_abstract_jac_add_equiv_h:  forall n p (rwnaf : list (t bool 16)),
      n < List.length rwnaf -> 
      Nat.div n numPrecompExponentGroups < Datatypes.length base_precomp_table -> 
      List.Forall (fun x => OddWindow wsize (sbvToInt _ x)) rwnaf -> 
      jac_eq 
        (seqToProd (add_base_abstract (Nat.pred wsize) rwnaf (prodToSeq (fromPoint p)) n))
        (fromPoint (Jacobian.add p (pExpMultiple (Nat.div n numPrecompExponentGroups) (sbvToInt _ (List.nth n rwnaf (vecRepeat 0%bool 16)))))).

      intros.
      unfold add_base_abstract, EC_P384_Abstract.add_base_abstract.
      match goal with
      | [|- context[nth_order ?a _]] => remember a as z
      end.

      rewrite select_point_affine_abstract_nth_equiv in Heqz.
      remember (List.nth n rwnaf (vecRepeat 0%bool 16)) as m.
      rewrite (@bvToNat_Z_to_nat_equiv 64 
       (sign_extend_16_64 (bvSShr 15 (bvAdd 16 (shiftR 16 bool 0%bool m 15) (bvXor 16 m (bvSShr 15 m 15))) 1))
       (sbvToInt _ (sign_extend_16_64
                 (bvSShr 15 (bvAdd 16 (shiftR 16 bool 0%bool m 15) (bvXor 16 m (bvSShr 15 m 15)))
                    1)))) in Heqz.
      rewrite sbvToInt_sign_extend_16_64_equiv in Heqz.
      rewrite (@bvSShr_Z_shiftr_equiv 15 (bvAdd 16 (shiftR 16 bool 0%bool m 15) (bvXor 16 m (bvSShr 15 m 15)))  (Z.abs (sbvToInt _ m)) 1 1%Z) in Heqz.
      rewrite F_cmovznz_equiv.
      eapply jac_eq_symm.
      eapply point_add_mixed_eq.
      erewrite nth_order_S_cons.
      erewrite nth_order_S_cons.
      erewrite nth_order_0_cons.
      trivial.

      rewrite seqToProd_inv.
      eapply jac_eq_refl.

      case_eq (bvEq 64 (point_id_to_limb_abstract (bvShr 16 m 15)) (intToBv 64 0)); intros.
      replace (cons EC_P384_Abstract.F (nth_order z zero_lt_two) 2
          (cons EC_P384_Abstract.F (nth_order z one_lt_two) 1 (cons EC_P384_Abstract.F 1 0 (nil EC_P384_Abstract.F))))
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
      replace (point_id_to_limb_abstract (intToBv 16 1)) with (intToBv 64 1) in *.
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
      unfold affineToJac.
      rewrite (@nth_indep _ (List.nth (n / numPrecompExponentGroups) base_precomp_table []) (Z.to_nat (BinInt.Z.shiftr (sbvToInt 16 (List.nth n rwnaf (vecRepeat 0%bool 16))) 1)) affine_default (cons F 0 1 (cons F 0 0 (nil F)))).
      eapply jac_eq_refl.
      specialize (@base_precomp_table_entry_length (List.nth (Nat.div n numPrecompExponentGroups) base_precomp_table [])); intros.

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
      replace (point_id_to_limb_abstract (intToBv 16 1)) with (intToBv 64 1) in *.
      assert (1 = 0)%Z.
      eapply intToBv_eq_pos; eauto.
      lia.
      lia.
      discriminate.
      reflexivity.
      lia.
      lia.

      eapply affineToJac_cons_eq.

      match goal with
      [|- jac_eq _ ?a ] => 
        replace a with (seqToProd (affineToJac (affineOpp z)))
      end.

      subst.
      unfold pExpMultiple.
      rewrite <- fromPoint_toPoint_id.
      unfold affineOppIfNegative, affinePointLookup.
      destruct (ZArith_dec.Z_lt_ge_dec (sbvToInt 16 (List.nth n rwnaf (vecRepeat 0%bool 16)))).
      rewrite Z.div2_spec.
      rewrite (@nth_indep _ (List.nth (n / numPrecompExponentGroups) base_precomp_table []) (Z.to_nat (BinInt.Z.shiftr (Z.abs (sbvToInt 16 (List.nth n rwnaf (vecRepeat 0%bool 16)))) 1)) affine_default (cons F 0 1 (cons F 0 0 (nil F)))).
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
      replace (point_id_to_limb_abstract (intToBv 16 0)) with (intToBv 64 0) in *.
      apply bvEq_neq in H2.
      intuition idtac.
      reflexivity.
      lia.
      lia.

      unfold affineToJac, affineOpp.
      simpl.
      reflexivity.

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
      (n' < List.length rwnaf <= numPrecompExponentGroups * (wsize * (Nat.pred wsize)))%nat -> 
      jac_eq 
        (seqToProd (add_base_abstract numPrecompExponentGroups rwnaf p1 n'))
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

    Theorem double_add_base_abstract_equiv : forall ls  rwnaf1 rwnaf2 x0 x n p1 p2,
      List.Forall (fun x => OddWindow wsize (sbvToInt _ x)) rwnaf2 -> 
      List.Forall (fun x => Nat.gcd x numPrecompExponentGroups = numPrecompExponentGroups) (List.map (fun x => x - n)%nat ls)  -> 
      List.Forall (fun x => x < Datatypes.length rwnaf2) ls -> 
      rwnaf1 = List.map (fun x => sbvToInt _ x) rwnaf2 -> 
      jac_eq (fromPoint p1) (seqToProd p2) ->
      multiSelect (signedWindowsToProg rwnaf1 0) ls = Some x0 ->
      decrExpLs n x0 = Some x -> 
      List.Forall2 (fun x y => Nat.div x numPrecompExponentGroups = Nat.div y numPrecompExponentGroups) ls (List.map (fun x => x - n)%nat ls) ->
      Datatypes.length rwnaf2 <= numPrecompExponentGroups * (wsize * (Nat.pred wsize)) ->
      jac_eq
        (fromPoint
           (groupMul_signedWindows_prog' wsize g p1 (x ++ [wm_Double 1])))
          (seqToProd
         (List.fold_left
            (add_base_abstract numPrecompExponentGroups
               rwnaf2)
            (List.rev ls)
            (List.fold_left
                (fun (x0 : Vec 3 (Vec 6 (Vec 64 bool))) (_ : nat) =>
                 point_double x0)
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
      eapply groupDouble_n_fold_left_double_equiv.
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
      eapply (add_base_abstract_jac_add_equiv _ _ _
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
      Datatypes.length rwnaf2 <= numPrecompExponentGroups * (wsize * (Nat.pred wsize)) ->
      jac_eq
        (fromPoint
           (groupMul_signedWindows_prog' wsize g p1 x))
          (seqToProd
         (List.fold_left
            (add_base_abstract numPrecompExponentGroups
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
      eapply (add_base_abstract_jac_add_equiv _ _ _
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

    Definition double_add_base_abstract := @double_add_base_abstract Fone Fadd Fsub Fmul Fdiv Fopp Finv _ a b _ F_cmovznz point_add point_double sign_extend_16_64 base_precomp_table select_point_affine_loop_body Fone.

    Theorem point_mul_base_abstract_list_equiv_h : forall x p p1 p2 rwnaf1 rwnaf2,
      jac_eq (fromPoint p1) (seqToProd p2) ->
      rwnaf1 = List.map (fun x => sbvToInt _ x) rwnaf2 -> 
      List.Forall (OddWindow wsize) rwnaf1 ->
      groupMul_signedWindows_prog' wsize g p1 (flatten x) = p ->
      permuteAndDouble_grouped rwnaf1 1
         (groupIndices_h (S (S (S nw))) numPrecompExponentGroups (List.length x)) = Some x ->
    Datatypes.length rwnaf2 <= numPrecompExponentGroups * (wsize * (Nat.pred wsize)) ->
      Datatypes.length rwnaf2 = (S (S (S nw))) -> 
      (Datatypes.length x) < (numPrecompExponentGroups) ->
    jac_eq (fromPoint p)
      (seqToProd
         (List.fold_left
            (double_add_base_abstract wsize (S (S (S nw)))
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
      
      unfold double_add_base_abstract, EC_P384_Abstract.double_add_base_abstract.
      destruct (PeanoNat.Nat.eq_dec (Datatypes.length x1) (Nat.pred (Nat.pred wsize))).
      unfold numPrecompExponentGroups in *.
      lia.
      
      apply (@double_add_base_abstract_equiv (lsMultiples (S (S (S nw))) (PeanoNat.Nat.pred wsize) (Datatypes.length x1)) (List.map (fun x : bitvector 16 => sbvToInt 16 x) rwnaf2) rwnaf2
        l0 x0 (Datatypes.length x1) p1 p2); intros.
     
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

    Theorem point_mul_base_abstract_list_equiv : forall x p p2 rwnaf1 rwnaf2,
      jac_eq (fromPoint zero_point) (seqToProd p2) ->
      rwnaf1 = List.map (fun x => sbvToInt _ x) rwnaf2 -> 
      List.Forall (OddWindow wsize) rwnaf1 ->
      groupMul_signedWindows_prog' wsize g zero_point (flatten x) == p ->
      permuteAndDouble_grouped rwnaf1 1
         (groupIndices_h (S (S (S nw))) numPrecompExponentGroups (List.length x)) = Some x ->
    Datatypes.length rwnaf2 <= numPrecompExponentGroups * (wsize * (Nat.pred wsize)) ->
    Datatypes.length rwnaf2 = (S (S (S nw))) ->
    (Datatypes.length x) <= (numPrecompExponentGroups) ->
    jac_eq (fromPoint p)
      (seqToProd
         (List.fold_left
            (double_add_base_abstract wsize (S (S (S nw)))
               rwnaf2)
            (forNats (List.length x))
            p2
      )).

      intros.
      destruct (PeanoNat.Nat.eq_dec (Datatypes.length x) numPrecompExponentGroups).  

      rewrite <- groupMul_signedWindows_prog_ls_equiv in H2.
      
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
      eapply (point_mul_base_abstract_list_equiv_h _ _ (groupMul_signedWindows_prog' wsize g zero_point l0)).
      unfold double_add_base_abstract, EC_P384_Abstract.double_add_base_abstract.
      
      destruct (PeanoNat.Nat.eq_dec (Datatypes.length l1) (Nat.pred (Nat.pred wsize))). 

      specialize (@ls_add_base_abstract_equiv (lsMultiples (S (S (S nw))) (PeanoNat.Nat.pred wsize) (Datatypes.length x1)) (List.map (fun x : bitvector 16 => sbvToInt 16 x) rwnaf2) rwnaf2
        l l0 (Datatypes.length l1) zero_point p2); intros.
      eapply jac_eq_trans.
      apply H10.
      eapply Forall_map.
      trivial.
      eapply Forall_map.
      rewrite H3.
      apply lsMultiples_gcd.
      eapply List.Forall_impl; [idtac | 
      apply lsMultiples_length_weak].
      intros.
      simpl in *; lia.
      reflexivity.
      trivial.
      apply H0.
      rewrite groupIndices_h_length in H8.
      rewrite <- H3.
      rewrite NPeano.Nat.mul_1_r in H8.
      trivial.
      apply Forall2_map_r.
      apply Forall2_same_Forall.
      rewrite H3.
      eapply lsMultiples_div.
      unfold numPrecompExponentGroups in *.
      lia.
      lia.
      lia. 
      rewrite H3.
      apply jac_eq_refl.

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

      eapply jac_eq_trans.
      eapply jacobian_eq_jac_eq.
      symmetry.
      eapply H2.
      eapply point_mul_base_abstract_list_equiv_h; eauto.
      lia.

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
       (@EC_P384_Abstract.point_opp_abstract Fopp x)) (fromPoint (Jacobian.opp y)).

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
      nth_order (@EC_P384_Abstract.point_opp_abstract Fopp p) pf = nth_order p pf.

      intros.
      unfold EC_P384_Abstract.point_opp_abstract.
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

    Definition point_mul_base_abstract := @point_mul_base_abstract Fone Fadd Fsub Fmul Fdiv Fopp Finv _ a b _ F_cmovznz point_add point_double sign_extend_16_64 base_precomp_table select_point_affine_loop_body Fone.

    Theorem point_mul_base_abstract_model_equiv : forall n x,
      (bvToInt 384 n < 2 ^ Z.of_nat (S (S (S nw)) * wsize))%Z ->
      groupedMul_scalar_precomp 1 (bvToNat _ n) = Some x ->
      S (S (S nw)) < numPrecompExponentGroups * (wsize * (Nat.pred wsize)) -> 
      jac_eq (fromPoint x)
    (seqToProd
       (point_mul_base_abstract wsize (S (S (S nw))) n)).

      intros.
      unfold point_mul_base_abstract, EC_P384_Abstract.point_mul_base_abstract,  groupedMul_scalar_precomp in *.
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
          (double_add_base_abstract wsize 
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
      
      specialize (@groupMul_signedWindows_prog'_equiv _ _ _ EC_CommutativeGroupWithDouble); intros.
      unfold idElem in H6.
      simpl in H6.
      rewrite H6.
      clear H6.
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
      apply OddWindow.
      apply wsize.
      lia.
      unfold numPrecompExponentGroups.
      lia.
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

      unfold EC_P384_Abstract.conditional_subtract_if_even_mixed_abstract.
      case_eq (Nat.even (bvToNat 384 n)); intros.
      rewrite H7 in H0.
      optSomeInv.
      eapply point_add_mixed_eq.
      rewrite nth_order_opp_eq; try lia.
      
      unfold EC_P384_Abstract.g.
      match goal with 
      | [|- context[Vector.append ?z _]] =>      
        erewrite (@nth_order_append_vec_ge _ 2%nat 1%nat z)
      end.
      rewrite nth_order_0_cons.
      eauto.
      lia.
      
      eauto.
      eapply jac_eq_symm.
      eapply jac_eq_fromPoint_opp.
      replace ((Vector.append
          (List.nth 0 (List.nth 0 base_precomp_table []) affine_default)
          (cons _ 1 0 (nil _))))
      with
      (affineToJac (List.nth 0 (List.nth 0 base_precomp_table []) affine_default)).
      
      unfold EC_P384_Abstract.g.
      eapply jac_eq_trans.
      apply base_precomp_table_correct.
      eauto.
      lia.
      unfold numPrecompExponentGroups.
      specialize (PeanoNat.Nat.pow_nonzero 2 (Nat.pred wsize)).
      intuition idtac.
      lia.
      rewrite NPeano.Nat.mul_0_r.
      rewrite NPeano.Nat.mul_0_l.
      Local Transparent Nat.pow.
      simpl.
      Local Opaque Nat.pow.
      eapply jacobian_eq_jac_eq.
      replace Jacobian.add with add.
      rewrite jac_add_comm.
      apply jac_add_id_l.
      reflexivity.
      generalize (List.nth 0 (List.nth 0 base_precomp_table []) affine_default); intros.
      unfold affineToJac.
      specialize (@SAWCorePrelude_proofs.rewrite_append _ _ _ (cons F 1 0 (nil F)) _ a0); intros.
      apply inj_pair2 in H0.
      unfold F in *.
      simpl in *.
      unfold Vec in *.
      unfold Bool in *.
      reflexivity.

      rewrite H7 in H0.
      optSomeInv.
      eauto.
      reflexivity.

      Unshelve.
      lia.

    Qed.

    Theorem groupMul_S_opp : forall x (p : Curve.point),
      Jacobian.eq (groupMul x p) (add (groupMul (S x) p) (opp p)).

      intros.
      simpl in *.
      rewrite jac_add_comm.
      
      unfold add.
      symmetry.
      transitivity (Jacobian.add (Jacobian.add (opp p) p) (groupMul x p)).
      symmetry.
      apply jac_add_assoc.
      transitivity (add zero_point (groupMul x p)).
      eapply Jacobian.Proper_add.
      transitivity (Jacobian.add p (opp p)).
      apply jac_add_comm.
      apply jac_opp_correct.
      reflexivity.
      apply jac_add_id_l.

    Qed.

    Definition pMultiple(z : Z) : Curve.point := pExpMultiple 0%nat z.

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
      S (S (S nw)) < numPrecompExponentGroups * (wsize * (Nat.pred wsize)) -> 
      groupedMul_scalar_precomp 1 (bvToNat 384 n) = Some p ->
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
      lia.
      rewrite bvToNat_toZ_equiv.
      rewrite Z.shiftl_1_l.
      eauto.

    Qed.

    Theorem point_mul_base_abstract_correct : forall n x,
      (bvToInt 384 n < 2 ^ Z.of_nat (S (S (S nw)) * wsize))%Z ->
      S (S (S nw)) < numPrecompExponentGroups * (wsize * (Nat.pred wsize)) -> 
      (groupedMul_scalar_precomp 1 (bvToNat 384 n)) = Some x -> 
      jac_eq (fromPoint (groupMul (bvToNat 384 n) g))
     (seqToProd (point_mul_base_abstract wsize (S (S (S nw))) n)).

      intros.

      eapply jac_eq_trans; [idtac | eapply point_mul_base_abstract_model_equiv]; eauto.
      eapply groupedMulScalar_precomp_groupMul_equiv; eauto.

    Qed.

  End EC_P384_Abstract_Model_equiv_wsize.

  (* Prove that base point multiplication succeeds with a window size of 5. *)
  Section EC_P384_Abstract_Model_equiv_5.

    Definition wsize := 5.
    Theorem wsize_range : (1 < wsize < 16)%nat.
      unfold wsize.
      lia.

    Qed.

    Definition nw := 74. (* actually (pred (pred (pred nw))) *)
    Theorem nw_range : nw <> 0%nat.
      unfold nw. lia.
    Qed.

        
    (* The base point and precomputed table of multiples of the base point *)
    Variable g : Curve.point.
    Variable  base_precomp_table : list (list affine_point).
    Hypothesis g_affine_jac_equiv :   
      jac_eq (seqToProd (affineToJac (@affine_g base_precomp_table))) (fromPoint g).

    (* Assume that the precomputed table has the correct length, each entry has the correct length, and the values in the table
    have been validated. *)
    Hypothesis base_precomp_table_length : List.length base_precomp_table = (wsize * (Nat.pred wsize))%nat.
    Hypothesis base_precomp_table_entry_length : 
      forall ls, List.In ls base_precomp_table -> List.length ls = Nat.pow 2 (Nat.pred wsize).
    Hypothesis base_precomp_table_validated : validate_base_table_abstract wsize base_precomp_table = true.

    Definition groupedMul_scalar_precomp_5 := @groupedMul_scalar_precomp
        wsize wsize_range nw nw_range g base_precomp_table g_affine_jac_equiv base_precomp_table_length base_precomp_table_entry_length base_precomp_table_validated.

    Theorem groupedMul_scalar_precomp_Some_P384_5 : forall n, exists x, 
      groupedMul_scalar_precomp_5 1 n = Some x.

      intros.
      unfold groupedMul_scalar_precomp_5.
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

  End EC_P384_Abstract_Model_equiv_5.

  (* Field inversion operation is correct. *)

  (* Assume that the field is finite with some particular field order that is not too small *)
  Variable field_order : nat.
  Hypothesis field_order_correct : forall x,
    Fpow field_order x = x.
  Hypothesis field_order_not_small  : 
    (field_order >= 3)%nat.

  (* Assume that the inverse square operation is correct *)
  Hypothesis felem_inv_sqr_abstract_eq_Fpow : forall x,
    @felem_inv_sqr_abstract Fmul x = Fpow (field_order - 3) x.

  Theorem pow_p_minus_3_eq_inv_sqr : forall x,
    x <> 0 -> 
    Fpow (field_order - 3) x = Finv (x^2).

    intros.
    replace (field_order - 3)%nat with (((field_order - 1) -1) -1)%nat.
    repeat rewrite Fpow_minus_1_div.
    rewrite field_div_definition.
    rewrite field_div_definition.
    rewrite field_div_definition.

    rewrite field_order_correct.

    rewrite (commutative x).
    rewrite left_multiplicative_inverse.
    rewrite left_identity.
    symmetry.
    apply inv_mul_eq.
    trivial.
    trivial.
    trivial.
    specialize (field_order_not_small); lia.
    trivial.
    specialize (field_order_not_small); lia.
    trivial.
    specialize (field_order_not_small); lia.
    trivial.
    specialize (field_order_not_small); lia.

  Qed.

  Theorem Fpow_2_square : forall z,
    Fpow 2 z = @Fsquare Fmul z.

    intros.
    simpl.
    unfold Fsquare.
    rewrite right_identity.
    reflexivity.

  Qed.

  Theorem Fsquare_n_S : forall n x,
    @Fsquare_n Fmul (S n) x = @Fsquare_n Fmul n (@Fsquare Fmul x).

    intros.
    reflexivity.

  Qed.

  Theorem Fsquare_n_S_rev : forall n x,
    @Fsquare_n Fmul (S n) x = @Fsquare Fmul (@Fsquare_n Fmul n x).

    induction n; intros; simpl.
    reflexivity.
    rewrite Fsquare_n_S.
    rewrite IHn.
    reflexivity.

  Qed.

  Theorem Fpow_mul_add : forall x y z,
    (Fpow x z) * (Fpow y z) = Fpow (x + y) z.

    induction x; intros; simpl.
    apply left_identity.
    rewrite <-associative.
    rewrite IHx.
    reflexivity.

  Qed.

  Theorem Fpow_2_b_Fsquare_n: forall n (z : F), Fpow (Nat.pow 2 n) z = @Fsquare_n Fmul n z.

    induction n; intros; simpl.
    unfold Fsquare_n.
    simpl.
    apply right_identity.
    rewrite Fsquare_n_S_rev.
    rewrite <- IHn.
    rewrite <- Fpow_2_square.
    simpl.
    rewrite right_identity.
    rewrite Fpow_mul_add.
    rewrite NPeano.Nat.add_0_r.
    reflexivity.

  Qed.

  Theorem Fpow_eq_mono_l : forall x y z, x = y -> Fpow x z = Fpow y z.
    
    intros.
    subst.
    reflexivity.

  Qed.

  Theorem Fpow_1_id : forall x,
    Fpow 1 x = x.

    intros.
    simpl.
    apply right_identity.

  Qed.

  
  Theorem felem_inv_sqr_abstract_correct : forall x,
    x <> 0 ->
    @felem_inv_sqr_abstract Fmul x = Finv (x^2).

    intros.
    rewrite felem_inv_sqr_abstract_eq_Fpow.
    apply pow_p_minus_3_eq_inv_sqr.
    trivial.

  Qed.

End EC_P384_Abstract_Model_equiv.

Section P384_inv_sqr_abstract_equiv.

  Context `{curve : Curve F Feq Fzero}.
  
  Definition p384_field_order :=  ((Nat.pow 2 384) - (Nat.pow 2 128) - (Nat.pow 2 96) + (Nat.pow 2 32) - 1)%nat.

  (* Assume that the field has the correct order *)
  Hypothesis p384_field_cyclic : forall x,
    Fpow p384_field_order x = x.

  Theorem p384_field_order_not_small : (p384_field_order >= 3)%nat.
    unfold p384_field_order.
    
    assert (Nat.pow 2 128 >= Nat.pow 2 96).
    apply PeanoNat.Nat.pow_le_mono_r; lia.
    assert (2 * (Nat.pow 2 128) = Nat.pow 2 129)%nat.
    rewrite <- PeanoNat.Nat.pow_succ_r'.
    reflexivity.
    assert (Nat.pow 2 384 - (Nat.pow 2 129) >= 4).
    unfold ge.
    transitivity (Nat.pow 2 129).
    replace 4 with (Nat.pow 2 2).
    apply PeanoNat.Nat.pow_le_mono_r.
    lia.
    lia.
    reflexivity.
    apply two_pow_minus.
    lia.
    lia.

  Qed.

  Local Opaque p384_field_order.

  Theorem felem_inv_sqr_abstract_eq_Fpow : forall x,
    @felem_inv_sqr_abstract Fmul x = Fpow (p384_field_order - 3) x.

    Local Opaque NPeano.Nat.pow Fpow.

    intros.
    unfold felem_inv_sqr_abstract.

    remember (Fmul (EC_P384_Abstract.Fsquare x) x) as x2.
    remember (Fmul (EC_P384_Abstract.Fsquare x2) x) as x3.
    remember (Fmul (Fsquare_n 3 x3) x3) as x6.
    remember (Fmul (Fsquare_n 6 x6) x6) as x12.
    remember (Fmul (Fsquare_n 3 x12) x3) as x15.
    remember (Fmul (Fsquare_n 15 x15) x15) as x30.
    remember (Fmul (Fsquare_n 30 x30) x30) as x60.
    remember (Fmul (Fsquare_n 60 x60) x60) as x120.
    remember (Fmul (Fsquare_n 120 x120) x120) as x240.
    remember (Fmul (Fsquare_n 15 x240) x15) as x255.

    assert (x2 = (Fpow (Nat.pow 2 2 - (Nat.pow 2 0)) x)).
    rewrite Heqx2.
    rewrite <- Fpow_2_square.
    replace x with (Fpow 1 x) at 2.
    rewrite Fpow_mul_add.
    reflexivity.
    apply Fpow_1_id.

    assert (x15 = (Fpow (Nat.pow 2 15 - (Nat.pow 2 0)) x)).
    rewrite Heqx15.

    assert (x3 = (Fpow (Nat.pow 2 3 - (Nat.pow 2 0)) x)).
    rewrite Heqx3.
    replace x with (Fpow 1 x) at 1.
    rewrite H.
    rewrite <- Fpow_2_square.
    erewrite <- (@Fpow_mul F Feq).
    replace 2%nat with (Nat.pow 2 1) at 1.
    rewrite PeanoNat.Nat.mul_sub_distr_l.
    repeat rewrite <- NPeano.Nat.pow_add_r.
    rewrite Fpow_mul_add.
    simpl.
    reflexivity.
    reflexivity.
    apply Feq_dec.
    apply Fpow_1_id.

    assert (x6 = (Fpow (Nat.pow 2 6 - (Nat.pow 2 0)) x)).
    rewrite Heqx6.
    rewrite H0.
    rewrite <- Fpow_2_b_Fsquare_n.
    rewrite <- (@Fpow_mul F Feq).
    rewrite Fpow_mul_add.
    apply Fpow_eq_mono_l.
    rewrite PeanoNat.Nat.mul_sub_distr_l.
    repeat rewrite <- NPeano.Nat.pow_add_r.
    simpl.
    repeat rewrite NPeano.Nat.add_sub_assoc.
    apply sub_eq_mono.
    apply PeanoNat.Nat.sub_add.
    apply PeanoNat.Nat.pow_le_mono_r; lia.
    reflexivity.
    apply PeanoNat.Nat.pow_le_mono_r; lia.
    apply Feq_dec.
    
    assert (x12 = (Fpow (Nat.pow 2 12 - (Nat.pow 2 0)) x)).
    rewrite Heqx12.
    rewrite H1.
    rewrite <- Fpow_2_b_Fsquare_n.
    rewrite <- (@Fpow_mul F Feq).
    rewrite Fpow_mul_add.
    apply Fpow_eq_mono_l.
    rewrite PeanoNat.Nat.mul_sub_distr_l.
    repeat rewrite <- NPeano.Nat.pow_add_r.
    simpl.
    repeat rewrite NPeano.Nat.add_sub_assoc.
    apply sub_eq_mono.
    apply PeanoNat.Nat.sub_add.
    apply PeanoNat.Nat.pow_le_mono_r; lia.
    reflexivity.
    apply PeanoNat.Nat.pow_le_mono_r; lia.
    apply Feq_dec.

    rewrite H2.
    rewrite H0.
    rewrite <- Fpow_2_b_Fsquare_n.
    rewrite <- (@Fpow_mul F Feq).
    rewrite Fpow_mul_add.
    apply Fpow_eq_mono_l.
    rewrite PeanoNat.Nat.mul_sub_distr_l.
    repeat rewrite <- NPeano.Nat.pow_add_r.
    simpl.
    repeat rewrite NPeano.Nat.add_sub_assoc.
    apply sub_eq_mono.
    apply PeanoNat.Nat.sub_add.
    apply PeanoNat.Nat.pow_le_mono_r; lia.
    reflexivity.
    apply PeanoNat.Nat.pow_le_mono_r; lia.
    apply Feq_dec.

    assert (x30 = (Fpow (Nat.pow 2 30 - (Nat.pow 2 0)) x)).
    rewrite Heqx30.
    rewrite H0.
    rewrite <- Fpow_2_b_Fsquare_n.
    rewrite <- (@Fpow_mul F Feq).
    rewrite Fpow_mul_add.
    apply Fpow_eq_mono_l.
    rewrite PeanoNat.Nat.mul_sub_distr_l.
    repeat rewrite <- NPeano.Nat.pow_add_r.
    simpl.
    repeat rewrite NPeano.Nat.add_sub_assoc.
    apply sub_eq_mono.
    apply PeanoNat.Nat.sub_add.
    apply PeanoNat.Nat.pow_le_mono_r; lia.
    reflexivity.
    apply PeanoNat.Nat.pow_le_mono_r; lia.
    apply Feq_dec.

    assert (x60 = (Fpow (Nat.pow 2 60 - (Nat.pow 2 0)) x)).
    rewrite Heqx60.
    rewrite H1.
    rewrite <- Fpow_2_b_Fsquare_n.
    rewrite <- (@Fpow_mul F Feq).
    rewrite Fpow_mul_add.
    apply Fpow_eq_mono_l.
    rewrite PeanoNat.Nat.mul_sub_distr_l.
    repeat rewrite <- NPeano.Nat.pow_add_r.
    simpl.
    repeat rewrite NPeano.Nat.add_sub_assoc.
    apply sub_eq_mono.
    apply PeanoNat.Nat.sub_add.
    apply PeanoNat.Nat.pow_le_mono_r; lia.
    reflexivity.
    apply PeanoNat.Nat.pow_le_mono_r; lia.
    apply Feq_dec.

    assert (x120 = (Fpow (Nat.pow 2 120 - (Nat.pow 2 0)) x)).
    rewrite Heqx120.
    rewrite H2.
    rewrite <- Fpow_2_b_Fsquare_n.
    rewrite <- (@Fpow_mul F Feq).
    rewrite Fpow_mul_add.
    apply Fpow_eq_mono_l.
    rewrite PeanoNat.Nat.mul_sub_distr_l.
    repeat rewrite <- NPeano.Nat.pow_add_r.
    simpl.
    repeat rewrite NPeano.Nat.add_sub_assoc.
    apply sub_eq_mono.
    apply PeanoNat.Nat.sub_add.
    apply PeanoNat.Nat.pow_le_mono_r; lia.
    reflexivity.
    apply PeanoNat.Nat.pow_le_mono_r; lia.
    apply Feq_dec.

    assert (x240 = (Fpow (Nat.pow 2 240 - (Nat.pow 2 0)) x)).
    rewrite Heqx240.
    rewrite H3.
    rewrite <- Fpow_2_b_Fsquare_n.
    rewrite <- (@Fpow_mul F Feq).
    rewrite Fpow_mul_add.
    apply Fpow_eq_mono_l.
    rewrite PeanoNat.Nat.mul_sub_distr_l.
    repeat rewrite <- NPeano.Nat.pow_add_r.
    simpl.
    repeat rewrite NPeano.Nat.add_sub_assoc.
    apply sub_eq_mono.
    apply PeanoNat.Nat.sub_add.
    apply PeanoNat.Nat.pow_le_mono_r; lia.
    reflexivity.
    apply PeanoNat.Nat.pow_le_mono_r; lia.
    apply Feq_dec.

    assert (x255 = (Fpow (Nat.pow 2 255 - (Nat.pow 2 0)) x)).
    rewrite Heqx255.
    rewrite H4.
    rewrite H0.
    rewrite <- Fpow_2_b_Fsquare_n.
    rewrite <- (@Fpow_mul F Feq).
    rewrite Fpow_mul_add.
    apply Fpow_eq_mono_l.
    rewrite PeanoNat.Nat.mul_sub_distr_l.
    repeat rewrite <- NPeano.Nat.pow_add_r.
    simpl.
    repeat rewrite NPeano.Nat.add_sub_assoc.
    apply sub_eq_mono.
    apply PeanoNat.Nat.sub_add.
    apply PeanoNat.Nat.pow_le_mono_r; lia.
    reflexivity.
    apply PeanoNat.Nat.pow_le_mono_r; lia.
    apply Feq_dec.

    rewrite H.
    rewrite H1.
    rewrite H5.

    repeat  rewrite <- Fpow_2_b_Fsquare_n.
    repeat  rewrite <- Fpow_2_square.
    rewrite <- (@Fpow_mul F Feq).
    rewrite <- (@Fpow_mul F Feq).
    rewrite <- (@Fpow_mul F Feq).
  
    rewrite PeanoNat.Nat.mul_sub_distr_l.
    repeat rewrite <- NPeano.Nat.pow_add_r.
    replace (2 * 2)%nat with (Nat.pow 2 2).
    simpl.
    rewrite Fpow_mul_add.
    rewrite <- (@Fpow_mul F Feq).
    rewrite PeanoNat.Nat.mul_add_distr_l.
    repeat rewrite PeanoNat.Nat.mul_sub_distr_l.
    rewrite Fpow_mul_add.
    rewrite <- (@Fpow_mul F Feq).
    rewrite Fpow_mul_add.
    rewrite <- (@Fpow_mul F Feq).
    repeat rewrite PeanoNat.Nat.mul_add_distr_l, PeanoNat.Nat.mul_sub_distr_l.
    repeat rewrite <- NPeano.Nat.pow_add_r.
    simpl.
    repeat rewrite PeanoNat.Nat.mul_sub_distr_l.
    repeat rewrite <- NPeano.Nat.pow_add_r.
    simpl.
    repeat rewrite NPeano.Nat.add_sub_assoc.
    Local Transparent p384_field_order.
    unfold p384_field_order.
    Local Opaque p384_field_order.
    rewrite <- NPeano.Nat.sub_add_distr.
    simpl.
    apply Fpow_eq_mono_l.
    apply sub_eq_mono; [idtac | reflexivity].
    apply add_eq_mono; [idtac | reflexivity].
    apply sub_eq_mono; [idtac | reflexivity].
    rewrite PeanoNat.Nat.sub_add.
    rewrite sub_add_assoc.
    rewrite (@PeanoNat.Nat.pow_succ_r' 2 128).
    simpl.
    rewrite NPeano.Nat.add_0_r.
    rewrite PeanoNat.Nat.add_sub.
    reflexivity.
    apply PeanoNat.Nat.pow_le_mono_r; lia.
    apply PeanoNat.Nat.pow_le_mono_r; lia.
    
    assert (NPeano.Nat.pow 2 98 <= NPeano.Nat.pow 2 128).   
    apply PeanoNat.Nat.pow_le_mono_r; lia.
    lia.
    apply PeanoNat.Nat.pow_le_mono_r; lia.
    apply PeanoNat.Nat.pow_le_mono_r; lia.
    apply PeanoNat.Nat.pow_le_mono_r; lia.

    apply Feq_dec.
    apply Feq_dec.
    apply Feq_dec.

    reflexivity.

    apply Feq_dec.
    apply Feq_dec.
    apply Feq_dec.

  Qed.

  Theorem felem_inv_sqr_abstract_correct_p384 : forall x,
    ~(Feq x Fzero) ->
    @felem_inv_sqr_abstract Fmul x = Finv (Fmul x x).

    intros.
    eapply felem_inv_sqr_abstract_correct.
    apply p384_field_cyclic.
    apply p384_field_order_not_small.
    apply felem_inv_sqr_abstract_eq_Fpow.
    trivial.
  Qed.

End P384_inv_sqr_abstract_equiv.
