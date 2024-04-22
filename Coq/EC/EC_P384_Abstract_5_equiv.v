(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0 *)

(* Proof of equivalence between the spec extracted from Cryptol and the hand-written
low-level specification in EC_P384_Abstract. *)

Set Implicit Arguments.

From Coq Require Import Lists.List.
From Coq Require Import String.
From Coq Require Import Vectors.Vector.
From Coq Require Import BinPos.
From Coq Require Import Ring.
From Coq Require Import Setoid.
From Coq Require Import ZArith.BinInt.
From Coq Require Import Classes.SetoidClass.
From Coq Require Import Lia.
From Coq Require Import BinNat.
From Coq Require Import BinPos.
From Coq Require Import Pnat.
From Coq Require Import Nat.
From Coq Require Import Arith.

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
Require Import CryptolToCoq.SAWCoreVectorsAsCoqVectors.

From EC Require Import Util.
From EC Require Import Curve.
From EC Require Import EC_P384_Abstract.
From EC Require Import EC_P384_5.
From EC Require Import CryptolToCoq_equiv.
From EC Require Import WindowedMulMachine.

Local Arguments cons [_] h [_] t.
Local Arguments append [m] [n] [a]%type_scope {Inh_a} x y.
Local Arguments bvOr [n] _ _.
Local Arguments bvAnd [n] _ _.
Local Arguments reverse [n] [a]%type_scope {Inh_a} _.
Local Arguments bvSub [n] _ _.
Local Arguments SAWCorePrelude.map [a]%type_scope {Inh_a} [b]%type_scope f%function_scope _ _.


Section EC_P384_Abstract_5_equiv.

  Definition F := Vec 6 (Vec 64 Bool).
  Definition Feq := (@eq F).
  Definition Fzero : F := (replicate 6 _ (replicate 64 _ false)).
  Existing Instance Feq_dec.
  Definition Fone := p384_felem_one.

  Context `{curve : Curve F Feq Fzero Fone}.
  Definition Fsquare := @Fsquare Fmul.

  Definition felem_inv_sqr_abstract := @felem_inv_sqr_abstract Fmul.

  Theorem felem_inv_sqr_abstract_equiv : forall x,
    felem_inv_sqr_abstract x = felem_inv_sqr Fsquare Fmul x.

    intros. 
    unfold felem_inv_sqr_abstract, EC_P384_Abstract.felem_inv_sqr_abstract, felem_inv_sqr.
    unfold Fsquare_n, EC_P384_Abstract.Fsquare_n.
    unfold Fsquare.
    reflexivity.

  Qed.

  Theorem point_id_to_limb_abstract_equiv : forall x,
    point_id_to_limb_abstract x = point_id_to_limb x.

    intros.
    unfold point_id_to_limb, point_id_to_limb_abstract.
    Local Opaque vecRepeat.
    simpl.
    eapply eq_if_to_list_eq.
    transitivity (to_list (vecRepeat 0%bool 48) ++ to_list x).
    eapply (VectorSpec.to_list_append _ _ _ (vecRepeat 0%bool 48) x); intros.
    symmetry.
    transitivity (to_list (intToBv 48 0) ++ to_list x).
    apply (toList_append_equiv _ (intToBv 48 0) x); intros.
    f_equal.

  Qed.

  Theorem mul_scalar_rwnaf_odd_loop_body_abstract_equiv : forall s,
    mul_scalar_rwnaf_odd_loop_body_abstract 5 s = mul_scalar_rwnaf_odd_loop_body s.

    intros.
    unfold mul_scalar_rwnaf_odd_loop_body, mul_scalar_rwnaf_odd_loop_body_abstract.
    removeCoerce.
    simpl.
    reflexivity.

  Qed.

  Theorem mul_scalar_rwnaf_odd_abstract_equiv : forall s,
    to_list (mul_scalar_rwnaf_odd s) = (mul_scalar_rwnaf_odd_abstract 5 74 s).

    intros.
    unfold mul_scalar_rwnaf_odd.
    repeat removeCoerce.

    Local Opaque append of_list ecFromTo.
    simpl.

    match goal with
    | [|- context[to_list (append ?v1 ?v2 )]] =>
      replace (to_list (append v1 v2 )) with (List.app (to_list v1) (to_list v2)); [idtac | symmetry; apply toList_append_equiv]
    end.

    rewrite toList_map_equiv.
    match goal with
    | [|- context[to_list (SAWCoreVectorsAsCoqVectors.scanl ?t1 ?t2 ?n ?f ?a ?v)]] =>
      replace (to_list (SAWCoreVectorsAsCoqVectors.scanl t1 t2 n f a v)) with (scanl f (to_list v) a); [idtac | symmetry; apply toList_scanl_equiv]
    end.

    rewrite ecFromTo_0_n_equiv.
    rewrite sawAt_nth_equiv.
    rewrite toList_reverse_equiv.
    rewrite nth_0_hd_equiv.
    match goal with
    | [|- context[to_list (SAWCoreVectorsAsCoqVectors.scanl ?t1 ?t2 ?n ?f ?a ?v)]] =>
      replace (to_list (SAWCoreVectorsAsCoqVectors.scanl t1 t2 n f a v)) with (scanl f (to_list v) a); [idtac | symmetry; apply toList_scanl_equiv]
    end.

    rewrite <- mul_scalar_rwnaf_odd_loop_body_abstract_equiv.
    rewrite (scanl_ext _ (fun (__p2 : bitvector 16 * bitvector 384) (_ : Integer) =>
        mul_scalar_rwnaf_odd_loop_body_abstract 5 (snd __p2))).

    rewrite ecFromTo_0_n_equiv.
    reflexivity.

    intros.
    symmetry.
    apply mul_scalar_rwnaf_odd_loop_body_abstract_equiv.

    lia.

  Qed.

  Theorem mul_scalar_rwnaf_equiv : forall s,
    to_list (mul_scalar_rwnaf s) = mul_scalar_rwnaf_abstract 5 74 s.

    intros.
    unfold mul_scalar_rwnaf.
    rewrite mul_scalar_rwnaf_odd_abstract_equiv.
    Local Opaque mul_scalar_rwnaf_odd_abstract.
    simpl.
    reflexivity.

  Qed.

  Definition select_point_abstract := select_point_abstract select_point_loop_body.

  Theorem select_point_abstract_equiv : forall x t,
    select_point x t = select_point_abstract x (to_list t).

    intros.
    unfold select_point, select_point_abstract.
    removeCoerce.
    rewrite ecFoldl_foldl_equiv.
    rewrite toList_zip_equiv. 

    replace ((to_list
          (ecFromTo 0%nat 15%nat (CryptolPrimitivesForSAWCore.seq 64%nat Bool)
             (PLiteralSeqBool 64%nat))))
    with (toN_excl_bv 64%nat (List.length (to_list t))).
    reflexivity.
    rewrite length_to_list.
    symmetry.
    apply (@ecFromTo_0_n_bv_excl_equiv 64%nat 15%nat).
  Qed.

  Definition point_mul := point_mul Fsquare Fmul Fsub Fadd Fopp.
 

  Definition conditional_subtract_if_even := 
    conditional_subtract_if_even Fsquare Fmul Fsub Fadd Fopp.

  Definition point_add := 
    point_add Fsquare Fmul Fsub Fadd.
  Definition point_double := 
    point_double Fsquare Fmul Fsub Fadd.

  Definition point_opp_abstract := @point_opp_abstract Fopp.

  Theorem conditional_subtract_if_even_equiv : forall (p1 : point) n (p2 : point),
    conditional_subtract_if_even p1 n p2 = 
    if (even (bvToNat _ n)) then (point_add false p1 (point_opp_abstract p2)) else p1.

    intros.
    unfold conditional_subtract_if_even, EC_P384_5.conditional_subtract_if_even.
    unfold felem_cmovznz.
    simpl.
    match goal with
    | [|- context[Vector.cons (if ?a then _ else _) _ ]] =>
      case_eq a; intros
    end.
    unfold ecEq, ecAnd, ecZero, byte_to_limb in H. simpl in H.
    case_eq (even (bvToNat 384%nat n)); intros.
    (* both even *)
    simpl.
    Local Transparent of_list.
    rewrite sawAt_3_equiv.
    repeat erewrite sawAt_nth_order_equiv.
    reflexivity.

    (* contradiction *)
    assert (Nat.pred 384 < 384)%nat by lia.
    erewrite (lsb_0_even _ H1) in H0.
    discriminate.
    eapply bvEq_nth_order in H.
    erewrite (@nth_order_append_eq _ _ 8%nat _ 56%nat) in H.
    erewrite nth_order_bvAnd_eq in H.
    erewrite nth_order_drop_eq in H.
    rewrite H.
    apply nth_order_0.
 
    case_eq (even (bvToNat 384%nat n)); intros.
    (* contradiction *)
    simpl in *.
    unfold ecEq, ecAnd, ecZero, byte_to_limb in H. simpl in H.
    assert (Nat.pred 384 < 384)%nat by lia.
    erewrite (lsb_1_not_even _ H1) in H0.
    discriminate.
    apply bvEq_false_ne in H.
    destruct H.
    destruct H.
    rewrite nth_order_0 in H.
    destruct (lt_dec x 56).
    erewrite (@nth_order_append_l_eq _ _ 8%nat _ 56%nat) in H.
    rewrite nth_order_0 in H.
    intuition idtac.
    assert (exists x', x = addNat x' 56)%nat.
    exists (x - 56)%nat.
    rewrite addNat_add.
    lia.
    destruct H2.
    subst.

    assert (x1 < 8)%nat.
    clear H.
    rewrite addNat_add in x0.
    lia.
    erewrite (@nth_order_append_eq _ _ 8%nat _ 56%nat _ _ _ H2) in H. 
    destruct (lt_dec x1 7)%nat. 
    erewrite nth_order_bvAnd_l_eq in H.
    intuition idtac.
    trivial.
    assert (x1 = (Nat.pred 8))%nat.
    rewrite addNat_add in x0.
    lia.
    subst.
    erewrite nth_order_bvAnd_eq in H.
    erewrite nth_order_drop_eq in H.
    apply Bool.not_false_is_true.
    eauto.

    (* both odd. *)
    unfold of_list.
    apply sawAt_3_equiv.

    Unshelve.
    lia.
    lia.
    lia.
    rewrite addNat_add.
    lia.
    lia.
    trivial.

  Qed.

  Definition pre_comp_table := pre_comp_table Fsquare Fmul Fsub Fadd.
  Definition pre_comp_table_abstract := pre_comp_table_abstract point_add point_double.

  Theorem pre_comp_table_abstract_equiv : forall p,
    to_list (pre_comp_table p) = pre_comp_table_abstract 14%nat p.

    intros. 
    unfold pre_comp_table_abstract, pre_comp_table, EC_P384_5.pre_comp_table, EC_P384_Abstract.pre_comp_table_abstract.
    removeCoerce.
    removeCoerce.
    rewrite toList_scanl_equiv.
    replace (List.map (BinIntDef.Z.add (BinIntDef.Z.of_nat 1)) (toN_int 14))
      with (to_list (ecFromTo (TCNum 1%nat) (TCNum 15%nat) Integer PLiteralInteger)).
    reflexivity.
    apply ecFromTo_m_n_equiv.
  Qed.

  Definition double_add_body := 
    double_add_body Fsquare Fmul Fsub Fadd Fopp.
  Definition double_add_body_abstract := 
    @double_add_body_abstract Fopp felem_cmovznz select_point_loop_body point_add point_double sign_extend_16_64.
  
  Local Opaque sign_extend_16_64 shiftR bvSShr select_point select_point_abstract bvAdd bvXor EC_P384_5.point_add List.fold_left.

  Theorem double_add_body_abstract_equiv : forall t p id,
    double_add_body t p id = double_add_body_abstract 4 (to_list t) p id.

    intros.
    unfold double_add_body, EC_P384_5.double_add_body.
    removeCoerce.
    rewrite ecFoldl_foldl_equiv.

    replace (to_list (ecFromTo 0%nat 4%nat Integer PLiteralInteger))
      with (toN_int 4%nat).
    unfold double_add_body_abstract, EC_P384_Abstract.double_add_body_abstract.
    repeat rewrite select_point_abstract_equiv.
    unfold point_add.
    unfold conditional_point_opp_abstract.
    simpl.
    repeat erewrite sawAt_nth_order_equiv.
    reflexivity.

    reflexivity.

    Unshelve.
    lia.

  Qed.

  Definition point_mul_abstract := 
    @point_mul_abstract Fopp felem_cmovznz select_point_loop_body point_add point_double sign_extend_16_64 conditional_subtract_if_even.

  Theorem point_mul_abstract_equiv : forall p s,
    point_mul p s = point_mul_abstract 5 74 14 p s.

    intros.
    unfold point_mul, EC_P384_5.point_mul, point_mul_abstract, EC_P384_Abstract.point_mul_abstract.

    rewrite ecFoldl_foldl_equiv.

    simpl.
    rewrite (fold_left_ext _
      (double_add_body_abstract 4%nat
        (pre_comp_table_abstract 14%nat p))
    ).
    rewrite toList_drop_equiv.
    rewrite toList_reverse_equiv.
    rewrite mul_scalar_rwnaf_equiv.

    rewrite select_point_abstract_equiv.
    rewrite pre_comp_table_abstract_equiv.

    unfold point_mul_abstract.
    rewrite sawAt_nth_equiv.
    rewrite mul_scalar_rwnaf_equiv.

    rewrite sawAt_nth_equiv.
    rewrite pre_comp_table_abstract_equiv.

    reflexivity.

    lia.
    lia.

    intros.
    rewrite <- pre_comp_table_abstract_equiv.
    unfold pre_comp_table.
  
    rewrite <- double_add_body_abstract_equiv.
    reflexivity.

  Qed.


  Definition double_add_base := double_add_base Fsquare Fmul Fsub Fadd Fopp.
  Definition point_mul_base := point_mul_base Fsquare Fmul Fsub Fadd Fopp.
  Definition add_base := add_base Fsquare Fmul Fsub Fadd Fopp.

  (* To avoid problems related to conversion performance, we assume a table using lists that is equivalent
  to the pre-computed table using vectors*)
  Variable base_precomp_table : list (list affine_point).
  Definition list_vec_eq (A : Type) n a (b : Vector.t A n) :=
    a = (to_list b).
  Hypothesis base_precomp_table_correct : 
    List.Forall2 (@list_vec_eq _ _) base_precomp_table (to_list p384_g_pre_comp).

  Global Opaque p384_g_pre_comp.

  Theorem base_precomp_table_length :
    List.length base_precomp_table = 20%nat.

   erewrite Forall2_length; eauto.
   reflexivity.
  Qed.

  Theorem base_precomp_table_nth_eq : forall i1 def1,
    (i1 < 20)%nat ->
    List.nth i1 base_precomp_table def1 = 
    to_list (@sawAt  _ _ _ p384_g_pre_comp i1).

    intros.
    eapply Forall2_nth_lt in base_precomp_table_correct.
    unfold list_vec_eq in *.
    rewrite base_precomp_table_correct.
    erewrite sawAt_nth_equiv.
    erewrite nth_indep.
    reflexivity.
    eapply H.
    lia.
    rewrite base_precomp_table_length.
    lia.
   
    Unshelve.
    apply (vecRepeat (cons Fzero (cons Fzero (@nil _)))).
 
  Qed.

  Theorem zip_equiv : forall (A B : Type)(inha : Inhabited A)(inhb : Inhabited B) n (va : Vector.t A n)(vb : Vector.t B n),
    EC_P384_5.zip n A B va vb = zip n va vb.

    intros.
    reflexivity.

  Qed.
  
  Definition select_point_affine_abstract := @select_point_affine_abstract Fone Fadd Fsub Fmul Fdiv Fopp Finv _ a b _ select_point_affine_loop_body.

  Theorem select_point_affine_abstract_equiv : forall x t,
    select_point_affine x t = select_point_affine_abstract x (to_list t).

    intros.
    unfold select_point_affine.
    unfold select_point_affine_abstract, EC_P384_Abstract.select_point_affine_abstract.
    rewrite ecFoldl_foldl_equiv.
    match goal with
    | [|- List.fold_left ?f1 ?l1?a1 = List.fold_left ?f2 ?l2 ?a2] =>
      replace l1 with l2
    end.
    reflexivity.
    rewrite length_to_list.
    rewrite zip_equiv.
    rewrite toList_zip_equiv.
    reflexivity.

  Qed.

  Definition add_base_abstract :=  
    @add_base_abstract  Fone Fadd Fsub Fmul Fdiv Fopp Finv _ a b _ felem_cmovznz point_add sign_extend_16_64 base_precomp_table select_point_affine_loop_body.

  Local Opaque vecRepeat.

  Theorem add_base_abstract_equiv : forall rnaf p i,
    (bvToNat _ i < 77)%nat -> 
    add_base_abstract p384_felem_one 4 (to_list rnaf) p (bvToNat _ i) = add_base rnaf p i.

    intros.
    unfold add_base_abstract, EC_P384_Abstract.add_base_abstract, add_base, EC_P384_5.add_base.
    unfold point_add.
    f_equal.
    f_equal.
    simpl.
    rewrite (sawAt_nth_order_equiv _ _ zero_lt_two).
    f_equal.
    rewrite select_point_affine_abstract_equiv.
    unfold select_point_affine_abstract.
    unfold ecPlus, ecXor.
    simpl.
    erewrite sawAt_nth_equiv.
    erewrite nth_indep.
    f_equal.
    rewrite base_precomp_table_nth_eq.
    f_equal.
    f_equal.
    unfold ecDiv.
    simpl.
    rewrite bvUDiv_nat_equiv.
    rewrite bvToNat_bvNat.
    reflexivity.

    replace (bvToNat 64 (intToBv 64 4)) with 4%nat.
    destruct (eq_nat_dec (bvToNat 64 i) O).
    rewrite e.
    rewrite Nat.div_0_l.
    eapply (@lt_le_trans _ (2^1)%nat).
    simpl.
    lia.
    apply Nat.pow_le_mono_r.
    lia.
    lia.
    lia.

    eapply lt_le_trans.
    eapply Nat.div_lt.
    lia.
    lia.
    eapply Nat.lt_le_incl.
    apply bvToNat_bounds.
    reflexivity.
    replace (fst (Nat.divmod (bvToNat 64 i) 3 0 3)) with ((bvToNat 64 i) / 4)%nat.
    apply Nat.div_lt_upper_bound; intros.
    lia.
    lia.
    reflexivity.
    rewrite length_to_list.
    lia.
    lia.

    simpl.
    repeat rewrite select_point_affine_abstract_equiv.
    replace (fst (Nat.divmod (bvToNat 64 i) 3 0 3))%nat with ((bvToNat 64 i) / 4)%nat.
    rewrite sawAt_nth_equiv.
    replace ((ecDiv (bitvector 64) (PIntegralWord 64) i (intToBv 64 4))) with (bvUDiv _ i (intToBv 64 4)).
    rewrite bvUDiv_nat_equiv.
    rewrite bvToNat_bvNat.
    rewrite (sawAt_nth_order_equiv _ _ one_lt_two).
    rewrite sawAt_nth_equiv.
    repeat rewrite <- bvShr_shiftR_equiv.
    f_equal.
    f_equal.
    f_equal.
    unfold select_point_affine_abstract.
    f_equal.
    f_equal.
    rewrite base_precomp_table_nth_eq.
    unfold Op_modulez20Uparameterz20Up384zugzuprezucomp.
    f_equal.
    rewrite sawAt_nth_equiv.
    reflexivity.
    apply Nat.div_lt_upper_bound. 
    lia.
    lia.
    apply Nat.div_lt_upper_bound. 
    lia.
    lia.
    
    f_equal.
    unfold select_point_affine_abstract.
    f_equal.
    f_equal.
    rewrite base_precomp_table_nth_eq.
    unfold Op_modulez20Uparameterz20Up384zugzuprezucomp.
    f_equal.
    rewrite sawAt_nth_equiv.
    reflexivity.
    apply Nat.div_lt_upper_bound. 
    lia.
    lia.
    apply Nat.div_lt_upper_bound. 
    lia.
    lia.

    apply Nat.div_lt_upper_bound. 
    replace (bvToNat 64 (intToBv 64 4)) with 4%nat.
    lia.
    reflexivity.
    replace (bvToNat 64 (intToBv 64 4)) with 4%nat.
    simpl.
    lia.
    reflexivity.
    apply Nat.div_lt_upper_bound. 
    replace (bvToNat 64 (intToBv 64 4)) with 4%nat.
    lia.
    reflexivity.
    
    replace (bvToNat 64 (intToBv 64 4)) with 4%nat.
    replace (bvToNat 64 i) with (1 * bvToNat 64 i)%nat.
    eapply le_lt_trans.
    eapply mult_le_compat_r.
    assert (1 <= 4)%nat by lia. eauto.
    eapply mult_lt_compat_l.
    apply bvToNat_bounds.
    lia.
    simpl.
    lia.
    reflexivity.

    reflexivity.
    trivial.
    reflexivity.
  Qed.

  Definition conditional_subtract_if_even_mixed := 
    conditional_subtract_if_even_mixed Fsquare Fmul Fsub Fadd Fopp.

  Theorem conditional_subtract_if_even_mixed_eq_compat : forall x1 x2 y1 y2 z1 z2,
    x1 = x2 ->
    y1 = y2 ->
    z1 = z2 ->
      conditional_subtract_if_even_mixed x1 y1 z1 =  conditional_subtract_if_even_mixed x2 y2 z2.

    intros.
    subst.
    reflexivity.

  Qed.

  Definition conditional_subtract_if_even_mixed_abstract := 
    @conditional_subtract_if_even_mixed_abstract Fopp point_add.

  Theorem conditional_subtract_if_even_mixed_equiv : forall (p1 : point) n (p2 : point),
    conditional_subtract_if_even_mixed p1 n p2 = 
    conditional_subtract_if_even_mixed_abstract p1 n p2.

    intros.
    unfold conditional_subtract_if_even_mixed_abstract, EC_P384_Abstract.conditional_subtract_if_even_mixed_abstract.
    unfold conditional_subtract_if_even_mixed, EC_P384_5.conditional_subtract_if_even_mixed.
    unfold felem_cmovznz.
    simpl.
    match goal with
    | [|- context[Vector.cons (if ?a then _ else _) _ ]] =>
      case_eq a; intros
    end.
    unfold ecEq, ecAnd, ecZero, byte_to_limb in H. simpl in H.
    case_eq (even (bvToNat 384%nat n)); intros.
    (* both even *)
    simpl.
    Local Transparent of_list.
    rewrite sawAt_3_equiv.
    unfold EC_P384_Abstract.point_opp_abstract.
    repeat erewrite sawAt_nth_order_equiv.
    reflexivity.
    
    (* contradiction *)
    assert (Nat.pred 384 < 384)%nat by lia.
    erewrite (lsb_0_even _ H1) in H0.
    discriminate.
    eapply bvEq_nth_order in H.
    erewrite (@nth_order_append_eq _ _ 8%nat _ 56%nat) in H.
    erewrite nth_order_bvAnd_eq in H.
    erewrite nth_order_drop_eq in H.
    rewrite H.
    apply nth_order_0.
 
    case_eq (even (bvToNat 384%nat n)); intros.
    (* contradiction *)
    simpl in *.
    unfold ecEq, ecAnd, ecZero, byte_to_limb in H. simpl in H.
    assert (Nat.pred 384 < 384)%nat by lia.
    erewrite (lsb_1_not_even _ H1) in H0.
    discriminate.
    apply bvEq_false_ne in H.
    destruct H.
    destruct H.
    rewrite nth_order_0 in H.
    destruct (lt_dec x 56).
    erewrite (@nth_order_append_l_eq _ _ 8%nat _ 56%nat) in H.
    rewrite nth_order_0 in H.
    intuition idtac.
    assert (exists x', x = addNat x' 56)%nat.
    exists (x - 56)%nat.
    rewrite addNat_add.
    lia.
    destruct H2.
    subst.

    assert (x1 < 8)%nat.
    clear H.
    rewrite addNat_add in x0.
    lia.
    erewrite (@nth_order_append_eq _ _ 8%nat _ 56%nat _ _ _ H2) in H. 
    destruct (lt_dec x1 7)%nat. 
    erewrite nth_order_bvAnd_l_eq in H.
    intuition idtac.
    trivial.
    assert (x1 = (Nat.pred 8))%nat.
    rewrite addNat_add in x0.
    lia.
    subst.
    erewrite nth_order_bvAnd_eq in H.
    erewrite nth_order_drop_eq in H.
    apply Bool.not_false_is_true.
    eauto.

    (* both odd. *)
    unfold of_list.
    apply sawAt_3_equiv.

    Unshelve.
    rewrite addNat_add.
    lia.
    lia.
    trivial.

  Qed.

  Definition double_add_base_abstract := 
    @double_add_base_abstract Fone Fadd Fsub Fmul Fdiv Fopp Finv _ a b _ felem_cmovznz point_add point_double sign_extend_16_64 base_precomp_table select_point_affine_loop_body.

  Theorem double_add_base_abstract_equiv : forall x y z,
    (bvToNat _ z < 4)%nat ->
    double_add_base_abstract p384_felem_one 5 77 (to_list x) y (bvToNat _ z) = double_add_base x y z.

    intros.
    unfold double_add_base_abstract, double_add_base, EC_P384_5.double_add_base.
    unfold ecEq, ecMinus in *.

    match goal with
    | [|- _ = if ?a then _ else _ ] =>
      case_eq a; intros
    end;
    simpl in H0;
     replace (bvSub (intToBv 64 4) (intToBv 64 1)) with (intToBv 64 3) in *.
    apply bvEq_eq in H0.     
    subst.
    rewrite ecFoldl_foldl_equiv.
    replace (bvToNat 64 (intToBv 64 3)) with 3%nat.
    unfold pred.
    destruct (Nat.eq_dec 3 3); try lia.
    eapply (@fold_left_R _ _ _ _ eq (fun x y => x = bvToNat _ y)).
    reflexivity.
    simpl.
    unfold to_list.
    repeat econstructor.
    intros.
    subst.
    apply add_base_abstract_equiv.
    eapply In_lsMultiples_if.
    eapply in_rev; eauto.
    reflexivity.
    reflexivity.

    match goal with
    | [|- _ = if ?a then _ else _ ] =>
      case_eq a; intros
    end;
    simpl in H1;
    replace (bvSub (intToBv 64 4) (intToBv 64 2)) with (intToBv 64 2) in *.
    apply bvEq_eq in H1.
    subst.
    rewrite ecFoldl_foldl_equiv.
    replace (bvToNat 64 (intToBv 64 2)) with 2%nat.
    unfold pred.
    destruct (Nat.eq_dec 2 3); try lia.
    eapply (@fold_left_R _ _ _ _ eq (fun x y => x = bvToNat _ y)).
    rewrite ecFoldl_foldl_equiv.
    eapply (@fold_left_R _ _ _ _ eq (fun x y => True)).
    reflexivity.
    simpl.
    Local Transparent ecFromTo.
    unfold ecFromTo.
    simpl.
    unfold to_list.
    repeat econstructor.
    intros.
    subst.
    reflexivity.
    simpl.
    unfold to_list.
    repeat econstructor.
    intros. 
    subst.
    apply add_base_abstract_equiv.
    eapply In_lsMultiples_if.
    eapply in_rev; eauto.
    reflexivity.
    reflexivity.

    match goal with
    | [|- _ = if ?a then _ else _ ] =>
      case_eq a; intros
    end;
    simpl in H2;
    replace (bvSub (intToBv 64 4) (intToBv 64 3)) with (intToBv 64 1) in *.
    apply bvEq_eq in H2.
    subst.
    rewrite ecFoldl_foldl_equiv.
    replace (bvToNat 64 (intToBv 64 1)) with 1%nat.
    unfold pred.
    destruct (Nat.eq_dec 1 3); try lia.
    eapply (@fold_left_R _ _ _ _ eq (fun x y => x = bvToNat _ y)).
    rewrite ecFoldl_foldl_equiv.
    eapply (@fold_left_R _ _ _ _ eq (fun x y => True)).
    reflexivity.
    simpl.
    Local Transparent ecFromTo.
    unfold ecFromTo.
    simpl.
    unfold to_list.
    repeat econstructor.
    intros.
    subst.
    reflexivity.
    simpl.
    unfold to_list.
    repeat econstructor.
    intros. 
    subst.
    apply add_base_abstract_equiv.
    eapply In_lsMultiples_if.
    eapply in_rev; eauto.
    reflexivity.
    reflexivity.

    match goal with
    | [|- _ = if ?a then _ else _ ] =>
      case_eq a; intros
    end;
    simpl in H3;
    replace (bvSub (intToBv 64 4) (intToBv 64 4)) with (intToBv 64 0) in *.
    apply bvEq_eq in H3.
    
    subst.
    rewrite ecFoldl_foldl_equiv.
    replace (bvToNat 64 (intToBv 64 0)) with 0%nat.
    unfold pred.
    destruct (Nat.eq_dec 0 3); try lia.
    eapply (@fold_left_R _ _ _ _ eq (fun x y => x = bvToNat _ y)).
    rewrite ecFoldl_foldl_equiv.
    eapply (@fold_left_R _ _ _ _ eq (fun x y => True)).
    reflexivity.
    simpl.
    Local Transparent ecFromTo.
    unfold ecFromTo.
    simpl.
    unfold to_list.
    repeat econstructor.
    intros.
    subst.
    reflexivity.
    simpl.
    unfold to_list.
    repeat econstructor.
    intros. 
    subst.
    apply add_base_abstract_equiv.
    eapply In_lsMultiples_if.
    eapply in_rev; eauto.
    reflexivity.
    reflexivity.

    apply bvEq_neq in H0.
    apply bvEq_neq in H1.
    apply bvEq_neq in H2.
    apply bvEq_neq in H3.
    exfalso.

    assert (bvToNat 64 z <> 0%nat).
    intuition idtac.
    eapply H3.
    rewrite <- (@bvNat_bvToNat _ z).
    rewrite H4.
    reflexivity.

    assert (bvToNat 64 z <> 1%nat).
    intuition idtac.
    eapply H2.
    rewrite <- (@bvNat_bvToNat _ z).
    rewrite H5.
    reflexivity.

    assert (bvToNat 64 z <> 2%nat).
    intuition idtac.
    eapply H1.
    rewrite <- (@bvNat_bvToNat _ z).
    rewrite H6.
    reflexivity.

    assert (bvToNat 64 z <> 3%nat).
    intuition idtac.
    eapply H0.
    rewrite <- (@bvNat_bvToNat _ z).
    rewrite H7.
    reflexivity.

    lia.

    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.

    (* This QED takes a minute or so --- could probably improve this with some induction instead of computation *)

  Qed.

  Definition point_mul_base_abstract := 
    @point_mul_base_abstract Fone Fadd Fsub Fmul Fdiv Fopp Finv _ a b _ felem_cmovznz point_add point_double sign_extend_16_64 base_precomp_table select_point_affine_loop_body.

  Definition g := g base_precomp_table p384_felem_one.

  Theorem point_mul_base_abstract_equiv : forall s,
    point_mul_base s = point_mul_base_abstract p384_felem_one 5 77 s.
    
    unfold point_mul_base, EC_P384_5.point_mul_base in *.
    unfold point_mul_base_abstract, EC_P384_Abstract.point_mul_base_abstract in *.
    unfold Op_modulez20Uparameterz20Up384zugzuprezucomp, Op_modulez20Uparameterz20Up384zufelemzuone in *.
    
    replace (append
     (sawAt 16 (Vec 2 (Vec 6 (bitvector 64)))
        (sawAt 20 (Vec 16 (Vec 2 (Vec 6 (bitvector 64)))) p384_g_pre_comp 0) 0)
     (cons p384_felem_one (nil (Vec 6 (bitvector 64))))) with g in *.
    intros.
    rewrite conditional_subtract_if_even_mixed_equiv.

    rewrite ecFoldl_foldl_equiv.
    unfold g.
    match goal with
    | [|- conditional_subtract_if_even_mixed_abstract ?a1 ?b ?c = EC_P384_Abstract.conditional_subtract_if_even_mixed_abstract _ ?a2 ?b ?c] =>
      replace a1 with a2
    end.  
    reflexivity.
    eapply (@fold_left_R _ _ _ _ eq (fun x y => x = bvToNat _ y)).
    reflexivity.
    simpl.
    unfold to_list.
    repeat econstructor.
    intros. subst.
    simpl.
    rewrite <- double_add_base_abstract_equiv.
    rewrite mul_scalar_rwnaf_equiv.
    reflexivity.
    simpl in *.
    intuition idtac; subst;
    match goal with
    | [|- (bvToNat 64 (intToBv 64 3) < 4)%nat ] =>
      replace (bvToNat 64 (intToBv 64 3))%nat with (3)%nat
    | [|- (bvToNat 64 (intToBv 64 2) < 4)%nat ] =>
      replace (bvToNat 64 (intToBv 64 2))%nat with (2)%nat
    | [|- (bvToNat 64 (intToBv 64 1) < 4)%nat ] =>
      replace (bvToNat 64 (intToBv 64 1))%nat with (1)%nat
    | [|- (bvToNat 64 (intToBv 64 0) < 4)%nat ] =>
      replace (bvToNat 64 (intToBv 64 0))%nat with (0)%nat
    end; simpl; try lia; try reflexivity.

    unfold g, EC_P384_Abstract.g.
    rewrite base_precomp_table_nth_eq.
    rewrite (@sawAt_nth_equiv _ _ 16).
    reflexivity.
    lia.
    lia.

  Qed.

  Definition felem_ne := felem_ne Fsub.

  Definition jacobian_affine_eq_abstract := 
    @jacobian_affine_eq_abstract Fone Fadd Fsub Fmul Fdiv Fopp Finv _ a b _ felem_nz.

  Theorem jacobian_affine_eq_abstract_equiv : forall jp ap,
    jacobian_affine_eq Fsquare Fmul Fsub jp ap = jacobian_affine_eq_abstract jp ap.

    intros.
    unfold jacobian_affine_eq.
    simpl.
    unfold ecNotEq, ecEq.
    simpl.
    repeat erewrite sawAt_nth_order_equiv in *.
    simpl in *.
    reflexivity.

    Unshelve.
    lia.
    lia.
    lia.
    lia.
    lia.

  Qed.


  Definition validate_base_row_body := validate_base_row_body Fsquare Fmul Fsub Fadd.
  Definition validate_base_row_body_abstract :=
    @validate_base_row_body_abstract  Fone Fadd Fsub Fmul Fdiv Fopp Finv _ a b _ point_add felem_nz.

  Theorem validate_base_row_body_abstract_equiv : forall g x y,
    validate_base_row_body g x y = validate_base_row_body_abstract g x y.

    intros.
    unfold validate_base_row_body, EC_P384_5.validate_base_row_body.
    unfold ecAnd.
    simpl.
    rewrite jacobian_affine_eq_abstract_equiv.
    reflexivity.

  Qed.

  Definition validate_base_row := validate_base_row Fsquare Fmul Fsub Fadd.
  Definition validate_base_row_abstract :=
    @validate_base_row_abstract  Fone Fadd Fsub Fmul Fdiv Fopp Finv _ a b _ point_add point_double felem_nz.
  
  Theorem validate_base_row_equiv : forall (p : point) r,
    validate_base_row p r = validate_base_row_abstract 5 p (to_list r).

    intros.
    unfold validate_base_row, EC_P384_5.validate_base_row, validate_base_row_abstract, EC_P384_Abstract.validate_base_row_abstract.
    rewrite ecFoldl_foldl_equiv.
    Local Opaque List.fold_left List.map inhabitant ecFromTo.
    simpl.
    rewrite toList_map_equiv.
    cut (forall ( A B : Type)(p1 p2 : A *B), p1 = p2 -> snd p1 = snd p2).
    intros.
    eapply H.
    eapply fold_left_f_equal.
    match goal with
    | [ |- List.map _ ?a = List.map _ ?b ] =>
      replace a with b
    end.
    eapply map_ext_in_iff.
    intros.
    eapply in_map_iff in H0.
    destruct H0.
    intuition idtac. 
    subst.
    apply in_toN_int in H2.
    intuition idtac.
    
    case_eq (intLe 0%Z (1 + x)%Z); intros.
    eapply sawAt_nth_equiv.
    lia.
    unfold intLe in *.
    apply Z.leb_gt in H2.
    lia.
    symmetry.
    eapply ecFromTo_m_n_equiv.
    f_equal.
    rewrite jacobian_affine_eq_abstract_equiv.
    unfold jacobian_affine_eq_abstract.
    f_equal.
    apply sawAt_nth_equiv.
    lia.
    intros. apply validate_base_row_body_abstract_equiv.
    intros. subst. reflexivity.

  Qed.

  Definition double_body := double_body Fsquare Fmul Fsub Fadd.
  Definition point_double_base_tsize := point_double_base_tsize Fsquare Fmul Fsub Fadd.

  Definition point_double_base_tsize_abstract :=
    point_double_base_tsize_abstract point_double.

  Theorem point_double_base_tsize_equiv : forall p,
    point_double_base_tsize p = point_double_base_tsize_abstract 20 p.

    intros.
    unfold point_double_base_tsize, EC_P384_5.point_double_base_tsize, point_double_base_tsize_abstract.
    rewrite ecFoldl_foldl_equiv.
    simpl.
    reflexivity.
  Qed.

  Definition validate_base_table_body := validate_base_table_body Fsquare Fmul Fsub Fadd.
  Definition validate_base_table_body_abstract :=
    @validate_base_table_body_abstract Fone Fadd Fsub Fmul Fdiv Fopp Finv _ a b _ point_add point_double felem_nz.


  Theorem validate_base_table_body_equiv : forall (st : point*bool) r,
    validate_base_table_body st r = validate_base_table_body_abstract 5 st (to_list r).

    intros.
    unfold validate_base_table_body, EC_P384_5.validate_base_table_body, validate_base_table_body_abstract, EC_P384_Abstract.validate_base_table_body_abstract.
    cut (forall (A B : Type) (a1 a2 : A)(b1 b2 : B), a1 = a2 -> b1 = b2 -> (a1, b1) = (a2, b2)).
    intros.
    eapply H.
    apply point_double_base_tsize_equiv.
    unfold ecAnd.
    simpl.
    cut (forall a b1 b2, b1 = b2 -> (a && b1 = a && b2)%bool); intros.
    apply H0.
    Local Opaque EC_P384_5.validate_base_row.
    eapply validate_base_row_equiv.
    subst. reflexivity.
    intros.
    subst. reflexivity.
  Qed.

  Definition validate_base_table := validate_base_table Fsquare Fmul Fsub Fadd.
  Definition validate_base_table_abstract :=
    @validate_base_table_abstract  Fone Fadd Fsub Fmul Fdiv Fopp Finv _ a b _ point_add point_double felem_nz.

  Theorem validate_base_table_equiv : forall t ls,
    List.Forall2 (@list_vec_eq _ _) ls (to_list t) ->
    validate_base_table t = validate_base_table_abstract 5 ls.

    intros.
    unfold validate_base_table, EC_P384_5.validate_base_table, validate_base_table_abstract, EC_P384_Abstract.validate_base_table_abstract.
    rewrite ecFoldl_foldl_equiv.
    simpl.
    f_equal.
    match goal with
    | [|- List.fold_left _ _ ?a = List.fold_left _ _ ?b] =>
      replace a with b
    end.
    symmetry.
    eapply fold_left_R; eauto.
    intros.
    subst.

    unfold list_vec_eq in *.
    subst.
    symmetry.
    apply validate_base_table_body_equiv.
    erewrite (@sawAt_nth_order_equiv _ _ 2%nat 0%nat).
    erewrite (@sawAt_nth_order_equiv _ _ 2%nat 1%nat).
    f_equal.
    apply affineToJac_cons_eq_gen.
    rewrite sawAt_nth_equiv.
    f_equal.
    rewrite sawAt_nth_equiv.
    eapply Forall2_nth_lt in H.
    unfold list_vec_eq in *.
    eapply H.
    erewrite Forall2_length; eauto.
    rewrite length_to_list.
    lia.
    lia.
    lia.

  Qed.

End EC_P384_Abstract_5_equiv.