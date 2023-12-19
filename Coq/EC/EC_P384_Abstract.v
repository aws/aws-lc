(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0 *)

(* Generalized low-level specification for NIST prime curve arithmetic. These functions
are equivalent to the functions extracted from Cryptol, and the following changes are made:
* Operations using Cryptol sequences are replaced with equivalent operations on vectors. 
* Vectors are replaced with lists in situations where a list is more natural (e.g. folding 
  over a list).
* Definitions are abstracted over window size, number of windows, word size, number of bits 
    used to represent the field, etc. 
*)

Set Implicit Arguments.

From Coq Require Import Lists.List.
From Coq Require Import String.
From Coq Require Import Vectors.Vector.
From Coq Require Import Vectors.VectorSpec.
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
From CryptolToCoq Require Import Everything.

From EC Require Import WindowedMulMachine.
From EC Require Import CryptolToCoq_equiv.
From EC Require Import EC_P384_5.


Local Arguments cons [_] h [_] t.
Local Arguments append [m] [n] [a]%type_scope {Inh_a} x y.
Local Arguments bvOr [n] _ _.
Local Arguments bvAnd [n] _ _.
Local Arguments reverse [n] [a]%type_scope {Inh_a} _.
Local Arguments bvSub [n] _ _.
Local Arguments SAWCorePrelude.map [a]%type_scope {Inh_a} [b]%type_scope f%function_scope _ _.

Definition mul_scalar_rwnaf_odd_loop_body_abstract (wsize : nat)(s : bitvector 384) :=
(drop Bool 368 16
   (bvSub
      (bvURem 384 s
         (bvMul 384 (bvNat 384 2)
            (shiftL 384 bool false (bvNat 384 1) wsize)))
      (shiftL 384 bool false (bvNat 384 1) wsize)),
shiftR 384 bool false
  (bvSub s
     (bvSub
        (bvURem 384 s
           (bvMul 384 (bvNat 384 2)
              (shiftL 384 bool false (bvNat 384 1) wsize)))
        (shiftL 384 bool false (bvNat 384 1) wsize))) wsize).

Theorem mul_scalar_rwnaf_odd_loop_body_abstract_equiv : forall s,
  mul_scalar_rwnaf_odd_loop_body_abstract 5 s = mul_scalar_rwnaf_odd_loop_body s.

  intros.
  unfold mul_scalar_rwnaf_odd_loop_body, mul_scalar_rwnaf_odd_loop_body_abstract.
  removeCoerce.
  simpl.
  reflexivity.

Qed.

From EC Require Import GroupMulWNAF.
From EC Require Import CryptolToCoq_equiv.
Require Import ZArith.BinInt.
Require Import BinNat.
Require Import BinPos.
Require Import Pnat.
Require Import Nat.
Require Import List.
Require Import Arith.

(* The abstract form of the double-and-add loop.
The function uses scanl to build a list of intermediate results and uses
hd to get the last result from the head of the list. The form of hd used
requires a default value that is returned when the list is empty (but the 
proof will show that the list is never empty). To produce this default value,
we use the Inhabited typeclass instances that proves that certain types are
inhabited, and the inhabitant function that produces a value from an inhabited 
type.
*)
Definition mul_scalar_rwnaf_odd_abstract wsize numWindows s :=
  List.map (fun x : bitvector 16 * bitvector 384 => fst x)
  (scanl
     (fun (__p2 : bitvector 16 * bitvector 384) (_ : Integer) =>
      mul_scalar_rwnaf_odd_loop_body_abstract wsize (snd __p2)) (toN_int numWindows)
     (mul_scalar_rwnaf_odd_loop_body_abstract wsize s)) ++
[drop Bool 368%nat 16%nat
   (snd
      (hd (inhabitant (Inhabited_prod (bitvector 16) (bitvector 384)))
         (rev
            (scanl
               (fun (__p2 : bitvector 16 * bitvector 384) (_ : Integer) =>
                mul_scalar_rwnaf_odd_loop_body_abstract wsize (snd __p2)) 
               (toN_int numWindows) (mul_scalar_rwnaf_odd_loop_body_abstract wsize s)))))].


Local Open Scope Z_scope.

Require Import Coq.ZArith.Zdigits.

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

Definition mul_scalar_rwnaf_abstract wsize nw s := 
  mul_scalar_rwnaf_odd_abstract wsize nw
    (bvOr s (intToBv 384%nat 1)).

Theorem mul_scalar_rwnaf_equiv : forall s,
  to_list (mul_scalar_rwnaf s) = mul_scalar_rwnaf_abstract 5 74 s.

  intros.
  unfold mul_scalar_rwnaf.
  rewrite mul_scalar_rwnaf_odd_abstract_equiv.
  Local Opaque mul_scalar_rwnaf_odd_abstract.
  simpl.
  reflexivity.

Qed.

Definition select_point_abstract x t :=
  fold_left
  (fun acc p =>
   select_point_loop_body x acc (fst p) (snd p))
  (combine (toN_excl_bv 64%nat (length t)) t) (of_list [zero_felem; zero_felem; zero_felem]).

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
  with (toN_excl_bv 64%nat (length (to_list t))).
  reflexivity.
  rewrite length_to_list.
  symmetry.
  apply (@ecFromTo_0_n_bv_excl_equiv 64%nat 15%nat).
Qed.

Require Import Coq.Logic.EqdepFacts.

Section PointMul.

  Definition felem := Vector.t (bitvector 64) 6.
  Definition prodPoint := (felem * felem * felem)%type.
  Definition point := Vector.t felem 3.
  Variable felem_sqr : felem -> felem.
  Variable felem_mul felem_sub felem_add : felem -> felem -> felem.
  Variable felem_opp : felem -> felem.

  Definition point_opp (p : point) : point :=
    Vector.cons (sawAt _ _ p 0%nat) 
      (Vector.cons (felem_opp (sawAt _ _ p 1%nat) ) 
        (Vector.cons (sawAt _ _ p 2%nat)  (Vector.nil felem))).

  Definition point_mul := point_mul felem_sqr felem_mul felem_sub felem_add felem_opp.
 
  Definition conditional_subtract_if_even := 
    conditional_subtract_if_even felem_sqr felem_mul felem_sub felem_add felem_opp.

  Definition point_add := 
    point_add felem_sqr felem_mul felem_sub felem_add.

  Theorem conditional_subtract_if_even_equiv : forall (p1 : point) n (p2 : point),
    conditional_subtract_if_even p1 n p2 = 
    if (even (bvToNat _ n)) then (point_add false p1 (point_opp p2)) else p1.

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
    apply sawAt_3_equiv.

    (* contradiction *)
    assert (pred 384 < 384)%nat by lia.
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
    assert (pred 384 < 384)%nat by lia.
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
    assert (x1 = (pred 8))%nat.
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

  Definition pre_comp_table := pre_comp_table felem_sqr felem_mul felem_sub felem_add .

  Definition pre_comp_table_abstract pred_tsize p :=
    scanl
  (fun
     (z : CryptolPrimitivesForSAWCore.seq 3%nat
            (CryptolPrimitivesForSAWCore.seq 6%nat
               (CryptolPrimitivesForSAWCore.seq 64%nat Bool))) 
     (_ : Integer) =>
   EC_P384_5.point_add felem_sqr felem_mul felem_sub felem_add
     (ecNumber 0%nat Bool PLiteralBit)
     (point_double felem_sqr felem_mul felem_sub felem_add p) z)
  (map (BinIntDef.Z.add (BinIntDef.Z.of_nat 1)) (toN_int pred_tsize)) p .

  Theorem pre_comp_table_abstract_equiv : forall p,
    to_list (pre_comp_table p) = pre_comp_table_abstract 14%nat p.

    intros. 
    unfold pre_comp_table_abstract, pre_comp_table, EC_P384_5.pre_comp_table.
    removeCoerce.
    removeCoerce.
    rewrite toList_scanl_equiv.
    replace (map (BinIntDef.Z.add (BinIntDef.Z.of_nat 1)) (toN_int 14))
      with (to_list (ecFromTo (TCNum 1%nat) (TCNum 15%nat) Integer PLiteralInteger)).
    reflexivity.
    apply ecFromTo_m_n_equiv.
  Qed.

  
  Definition double_add_body := 
    double_add_body felem_sqr felem_mul felem_sub felem_add felem_opp.
  

  Definition conditional_point_opp (t : bitvector 64) (p : point): point :=
    Vector.cons (sawAt _ _ p 0%nat) (Vector.cons (felem_cmovznz t (sawAt _ _ p 1%nat) (felem_opp (sawAt _ _ p 1%nat))) (Vector.cons (sawAt _ _ p 2%nat) (Vector.nil _))).

  Definition double_add_body_abstract pred_wsize t p id :=
    EC_P384_5.point_add felem_sqr felem_mul felem_sub
  felem_add false
  (fold_left
     (fun
        (x : CryptolPrimitivesForSAWCore.seq 3%nat
               (CryptolPrimitivesForSAWCore.seq 6%nat
                  (CryptolPrimitivesForSAWCore.seq 64%nat Bool)))
        (_ : Integer) =>
      point_double felem_sqr felem_mul felem_sub felem_add x)
     (toN_int pred_wsize) p)
  (conditional_point_opp
     (point_id_to_limb
        (shiftR 16 bool false id 15))
     (select_point_abstract
        (sign_extend_16_64
           (bvSShr 15%nat
              (bvAdd 16
                  (shiftR 16 bool false id 15)


                 (bvXor 16%nat id
                      (bvSShr 15%nat id 15)
)) 1%nat)) t)).

  Theorem double_add_body_abstract_equiv : forall t p id,
    double_add_body t p id = double_add_body_abstract 4 (to_list t) p id.

    intros.
    unfold double_add_body, EC_P384_5.double_add_body.
    removeCoerce.
    rewrite ecFoldl_foldl_equiv.

    replace (to_list (ecFromTo 0%nat 4%nat Integer PLiteralInteger))
      with (toN_int 4%nat).
    repeat rewrite select_point_abstract_equiv.
    reflexivity.

    symmetry.
    apply ecFromTo_0_n_equiv.

  Qed.

  Definition point_mul_abstract wsize nw pred_tsize p s : point := 
    EC_P384_5.conditional_subtract_if_even felem_sqr felem_mul
  felem_sub felem_add felem_opp
  (fold_left
     (double_add_body_abstract (pred wsize) (pre_comp_table_abstract pred_tsize p))
     (skipn 1 (rev (mul_scalar_rwnaf_abstract wsize nw s)))
     (select_point_abstract
        (sign_extend_16_64
           (bvSShr 15
              (nth (S (S nw)) (mul_scalar_rwnaf_abstract wsize nw s)
                 (bvNat 16%nat 0%nat))
              1%nat) )
        (pre_comp_table_abstract pred_tsize p))) s
  (nth 0 (pre_comp_table_abstract pred_tsize p)
     (inhabitant (ecNumber 0%nat Integer PLiteralInteger))).

  Theorem point_mul_abstract_equiv : forall p s,
    point_mul p s = point_mul_abstract 5 74 14 p s.

    intros.
    unfold point_mul, EC_P384_5.point_mul.

    rewrite ecFoldl_foldl_equiv.

    Local Opaque fold_left.
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

    Local Transparent fold_left.

  Qed.

  Section PointMulBase.

    Definition double_add_base := double_add_base felem_sqr felem_mul felem_sub felem_add felem_opp.
    Definition point_mul_base := point_mul_base felem_sqr felem_mul felem_sub felem_add felem_opp.
    Definition point_double := point_double felem_sqr felem_mul felem_sub felem_add.
    Definition add_base := add_base felem_sqr felem_mul felem_sub felem_add felem_opp.

    Definition affine_point := Vector.t felem 2.

    Local Transparent p384_g_pre_comp.
    Variable base_precomp_table : list (list affine_point).
    Hypothesis base_precomp_table_eq : 
      Forall2 (fun x y => x = to_list y) base_precomp_table (to_list p384_g_pre_comp).

    Theorem base_precomp_table_length :
      List.length base_precomp_table = 20%nat.

      intros.
      erewrite Forall2_length; eauto.
      apply length_to_list.

    Qed.

    Theorem base_precomp_table_nth_eq : forall i1 def1,
      (i1 < 20)%nat ->
      nth i1 base_precomp_table def1 = 
      to_list (@sawAt  _ _ _ p384_g_pre_comp i1).

      intros.
      erewrite sawAt_nth_equiv.
      eapply (@Forall2_nth_lt _ _ _ _ _ base_precomp_table_eq).
      rewrite base_precomp_table_length.
      trivial.
      trivial.

    Qed.

    Import VectorNotations. 
  
    Definition select_point_affine_abstract x t :=
      fold_left
      (fun acc p =>
       select_point_affine_loop_body x acc (fst p) (snd p))
      (combine (toN_excl_bv 64%nat (length t)) t) (of_list [zero_felem; zero_felem]).

    Theorem zip_equiv : forall (A B : Type)(inha : Inhabited A)(inhb : Inhabited B) n (va : Vector.t A n)(vb : Vector.t B n),
      EC_P384_5.zip n A B va vb = zip n va vb.

      intros.
      reflexivity.

    Qed.

    Theorem select_point_affine_abstract_equiv : forall x t,
      select_point_affine x t = select_point_affine_abstract x (to_list t).

      intros.
      unfold select_point_affine.
      unfold select_point_affine_abstract.
      rewrite ecFoldl_foldl_equiv.
      match goal with
      | [|- fold_left ?f1 ?l1?a1 = fold_left ?f2 ?l2 ?a2] =>
        replace l1 with l2
      end.
      reflexivity.
      rewrite length_to_list.
      rewrite zip_equiv.
      rewrite toList_zip_equiv.
      reflexivity.

    Qed.
  
    Theorem zero_lt_two: (0 < 2)%nat.
      intuition eauto.
    Qed.

    Theorem one_lt_two : (1 < 2)%nat.
      intuition eauto.
    Qed.

    Definition add_base_abstract one pred_wsize (rnaf : list (Vector.t bool 16))(p : point)(j : nat) : point :=
      let window  := nth j rnaf (vecRepeat false 16) in
      let selected   := select_point_affine_abstract (sign_extend_16_64 (bvSShr _ (bvAdd _ (shiftR _ _ false window 15) (bvXor _ window (bvSShr _ window 15%nat))) 1%nat)) (nth (Nat.div j pred_wsize) base_precomp_table nil) in
      let x_coord   :=nth_order  selected zero_lt_two in
      let y_coord   :=nth_order  selected one_lt_two in
      point_add true p [x_coord; felem_cmovznz (point_id_to_limb (bvShr _ window 15)) y_coord (felem_opp y_coord); one].

    Theorem add_base_abstract_equiv : forall rnaf p i,
      (bvToNat _ i < 77)%nat -> 
      add_base_abstract p384_felem_one 4 (to_list rnaf) p (bvToNat _ i) = add_base rnaf p i.

      intros.
      unfold add_base_abstract, add_base, EC_P384_5.add_base.
      unfold point_add.
      f_equal.
      f_equal.
      simpl.
      rewrite (sawAt_nth_order_equiv _ _ zero_lt_two).
      f_equal.
      rewrite select_point_affine_abstract_equiv.
      f_equal.
      f_equal.
      f_equal.
      simpl.
      unfold ecPlus.
      simpl.
      f_equal.
      erewrite sawAt_nth_equiv.
      erewrite nth_indep.
      reflexivity.
      rewrite length_to_list.
      trivial.
      trivial.
      unfold ecXor.
      simpl.
      erewrite sawAt_nth_equiv.
      erewrite nth_indep.
      reflexivity.
      rewrite length_to_list.
      trivial.
      trivial.
      erewrite base_precomp_table_nth_eq.
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
      simpl.
      lia.
      reflexivity.

      f_equal.
      f_equal.
      rewrite bvShr_shiftR_equiv.
      simpl.
      rewrite sawAt_nth_equiv.
      erewrite nth_indep.
      reflexivity.
      rewrite length_to_list.
      trivial.
      trivial.

      Local Opaque shiftR.
      simpl.
      erewrite sawAt_nth_order_equiv.
      f_equal.
      rewrite select_point_affine_abstract_equiv.
      unfold ecPlus.
      simpl.
      unfold ecXor.
      simpl.
      unfold ecZero.
      rewrite sawAt_nth_equiv.
      erewrite nth_indep.
      simpl.
      f_equal.
      replace (fst (Nat.divmod (bvToNat 64 i) 3 0 3))%nat with ((bvToNat 64 i) / 4)%nat.
      rewrite sawAt_nth_equiv.
      erewrite nth_indep.
      replace ((ecDiv (bitvector 64) (PIntegralWord 64) i (intToBv 64 4))) with (bvUDiv _ i (intToBv 64 4)).
      rewrite bvUDiv_nat_equiv.
      rewrite bvToNat_bvNat.
      unfold Op_modulez20Uparameterz20Up384zugzuprezucomp.
      rewrite base_precomp_table_nth_eq.
      rewrite sawAt_nth_equiv.
      reflexivity.
      apply Nat.div_lt_upper_bound; simpl; lia.
      apply Nat.div_lt_upper_bound; simpl; lia.
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
      reflexivity.
      erewrite Forall2_length; [idtac | apply base_precomp_table_eq].
      rewrite length_to_list.
      apply Nat.div_lt_upper_bound; simpl; lia.
      replace ((ecDiv (bitvector 64) (PIntegralWord 64) i (intToBv 64 4))) with (bvUDiv _ i (intToBv 64 4)).
      rewrite bvUDiv_nat_equiv.
      replace (bvToNat 64 (intToBv 64 4)) with 4%nat.
      rewrite bvToNat_bvNat.
      apply Nat.div_lt_upper_bound; simpl; lia.
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
      reflexivity.
      reflexivity.
      rewrite length_to_list.
      trivial.
      trivial.
      
      f_equal.
      simpl.
      rewrite (sawAt_nth_order_equiv _ _ one_lt_two).
      f_equal.
      rewrite select_point_affine_abstract_equiv.
      replace (fst (Nat.divmod (bvToNat 64 i) 3 0 3))%nat with ((bvToNat 64 i) / 4)%nat.
      rewrite sawAt_nth_equiv.
      replace ((ecDiv (bitvector 64) (PIntegralWord 64) i (intToBv 64 4))) with (bvUDiv _ i (intToBv 64 4)).
      rewrite bvUDiv_nat_equiv.
      rewrite bvToNat_bvNat.
      unfold Op_modulez20Uparameterz20Up384zugzuprezucomp.
      rewrite base_precomp_table_nth_eq.
      reflexivity.

      apply Nat.div_lt_upper_bound; simpl; lia.
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
      reflexivity.
      trivial.
      reflexivity.

      Unshelve.
      apply nil.

    Qed.


    Import VectorNotations. 
    
    Definition b8_114 := CryptolPrimitivesForSAWCore.ecNumber 114%nat _ (CryptolPrimitivesForSAWCore.PLiteralSeqBool 8%nat).
    Definition b8_110 := CryptolPrimitivesForSAWCore.ecNumber 110%nat _ (CryptolPrimitivesForSAWCore.PLiteralSeqBool 8%nat).
    Definition b8_104 := CryptolPrimitivesForSAWCore.ecNumber 104%nat _ (CryptolPrimitivesForSAWCore.PLiteralSeqBool 8%nat).
    Definition b8_101 := CryptolPrimitivesForSAWCore.ecNumber 101%nat _ (CryptolPrimitivesForSAWCore.PLiteralSeqBool 8%nat).
    Definition b8_99 := CryptolPrimitivesForSAWCore.ecNumber 99%nat _ (CryptolPrimitivesForSAWCore.PLiteralSeqBool 8%nat).
    Definition b8_98 := CryptolPrimitivesForSAWCore.ecNumber 98%nat _ (CryptolPrimitivesForSAWCore.PLiteralSeqBool 8%nat).
    Definition b8_97 := CryptolPrimitivesForSAWCore.ecNumber 97%nat _ (CryptolPrimitivesForSAWCore.PLiteralSeqBool 8%nat).
    Definition b8_32 := CryptolPrimitivesForSAWCore.ecNumber 32%nat _ (CryptolPrimitivesForSAWCore.PLiteralSeqBool 8%nat).
    Definition b64_4 := CryptolPrimitivesForSAWCore.ecNumber 4%nat _ (CryptolPrimitivesForSAWCore.PLiteralSeqBool 64%nat).
    Definition b64_3 := CryptolPrimitivesForSAWCore.ecNumber 3%nat _ (CryptolPrimitivesForSAWCore.PLiteralSeqBool 64%nat).

    Definition double_add_base_abstract one (wsize : nat) (nw : nat) rnaf
      (p : point) 
      (i : nat) 
        : point :=
    let doubled   := if (eq_nat_dec i (pred (pred wsize)))  then p else fold_left (fun x _ => point_double x) (forNats wsize) p  in
      fold_left (add_base_abstract one (pred wsize) rnaf) (List.rev (lsMultiples nw (pred wsize) i)) doubled.

    Definition p384_g_pre_comp_gen := p384_g_pre_comp.
    Local Opaque p384_g_pre_comp_gen.

    Definition conditional_subtract_if_even_mixed := 
      conditional_subtract_if_even_mixed felem_sqr felem_mul felem_sub felem_add felem_opp.


    Theorem conditional_subtract_if_even_mixed_eq_compat : forall x1 x2 y1 y2 z1 z2,
      x1 = x2 ->
      y1 = y2 ->
      z1 = z2 ->
        conditional_subtract_if_even_mixed x1 y1 z1 =  conditional_subtract_if_even_mixed x2 y2 z2.

      intros.
      subst.
      reflexivity.

    Qed.

    Definition conditional_subtract_if_even_mixed_abstract p1 n p2 :=
      if (even (bvToNat 384 n)) then (point_add true p1 (point_opp p2)) else p1.

   Theorem conditional_subtract_if_even_mixed_equiv : forall (p1 : point) n (p2 : point),
      conditional_subtract_if_even_mixed p1 n p2 = 
      conditional_subtract_if_even_mixed_abstract p1 n p2.

      intros.
      unfold conditional_subtract_if_even_mixed_abstract.
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
      apply sawAt_3_equiv.

      (* contradiction *)
      assert (pred 384 < 384)%nat by lia.
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
      assert (pred 384 < 384)%nat by lia.
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
      assert (x1 = (pred 8))%nat.
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

    Variable affine_default : Vec 2 felem.

    Definition affine_g one := Vector.append (nth 0 (nth 0 base_precomp_table nil) affine_default) [one].

    Definition point_mul_base_abstract one (wsize nw : nat)  s :=
      conditional_subtract_if_even_mixed_abstract 
      (fold_left
         (double_add_base_abstract one wsize nw (mul_scalar_rwnaf_abstract wsize (pred (pred (pred nw))) s))
          (forNats (pred wsize))
          (replicate 3 (Vec 6 (bitvector 64)) (replicate 6 (bitvector 64) (intToBv 64 0)))
      ) s (affine_g one).

  Theorem point_mul_base_abstract_equiv : forall s,
    point_mul_base s = point_mul_base_abstract p384_felem_one 5 77 s.
    
    unfold point_mul_base, EC_P384_5.point_mul_base in *.
    unfold point_mul_base_abstract in *.
    unfold Op_modulez20Uparameterz20Up384zugzuprezucomp in *.
    replace (append
     (sawAt 16 (Vec 2 (Vec 6 (bitvector 64)))
        (sawAt 20 (Vec 16 (Vec 2 (Vec 6 (bitvector 64)))) p384_g_pre_comp 0) 0)
     [p384_felem_one]) with (affine_g p384_felem_one) in *.
    intros.
    rewrite conditional_subtract_if_even_mixed_equiv.

    rewrite ecFoldl_foldl_equiv.
    match goal with
    | [|- conditional_subtract_if_even_mixed_abstract ?a1 ?b ?c = conditional_subtract_if_even_mixed_abstract ?a2 ?b ?c] =>
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

    unfold affine_g.
    rewrite base_precomp_table_nth_eq.
    rewrite (@sawAt_nth_equiv _ _ 16).
    reflexivity.
    lia.
    lia.

  Qed.

  End PointMulBase.

End PointMul.

