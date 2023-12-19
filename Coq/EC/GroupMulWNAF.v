(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0 *)

(* Definitions and facts related to optimized group multiplication. The main result is a proof that multiplication using windowed non-adjacent form is correct. *)

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
Require Import SetoidClass.

From EC Require Export Util.
From EC Require Export CommutativeGroup.

Definition SignedWindow := Z.


(* A simple definition of group multiplication, an optimized multiplication algorithm using 
windowed non-adjacent form, and a proof of equivalence of the two. *)
Section GroupMulWNAF.

  Context `{dbl_grp: CommutativeGroupWithDouble}.

  (* a basic double and add loop *) 

  Fixpoint groupMul_doubleAdd_pos(p : positive)(e : GroupElem) :=
    match p with
    | xI p' => groupAdd e (groupDouble (groupMul_doubleAdd_pos p' e))
    | xO p' => groupDouble (groupMul_doubleAdd_pos p' e)
    | xH => e
    end.

  Definition groupMul_doubleAdd(x : nat)(e : GroupElem) :=
    match (N.of_nat x) with
    | N0 => idElem
    | Npos p => groupMul_doubleAdd_pos p e
    end.


  Theorem groupMul_doubleAdd_pos_equiv : 
    forall p e,
    groupMul_doubleAdd_pos p e == groupMul (Pos.to_nat p) e.

    induction p; intuition; simpl in *.
    +rewrite IHp.
    apply groupAdd_proper.
    reflexivity.
    rewrite Pmult_nat_mult.
    rewrite PeanoNat.Nat.mul_comm.
    simpl.
    rewrite groupDouble_correct.
    rewrite PeanoNat.Nat.add_0_r.
    rewrite groupMul_distr.
    reflexivity.

    +rewrite IHp.
    rewrite Pos2Nat.inj_xO.
    rewrite groupDouble_correct.
    simpl.
    rewrite PeanoNat.Nat.add_0_r.
    rewrite groupMul_distr.
    reflexivity.

    +rewrite groupAdd_comm.
    rewrite groupAdd_id.
    reflexivity.

  Qed.


  Theorem groupMul_doubleAdd_correct : 
    forall x e,
    groupMul_doubleAdd x e == groupMul x e.

    unfold groupMul_doubleAdd in *. intros.
    destruct x; simpl in *; trivial.
    reflexivity.

    rewrite groupMul_doubleAdd_pos_equiv.
    rewrite SuccNat2Pos.id_succ.
    simpl.
    reflexivity.
  Qed.
  
  Fixpoint groupMul_doubleAdd_bits(bs : list bool)(e : GroupElem) :=
    match bs with
    | nil => idElem
    | b :: bs' =>
      let e' := (groupDouble (groupMul_doubleAdd_bits bs' e)) in
      match b with
      | false => e'
      | true => groupAdd e e'
      end
    end.


  Theorem groupMul_doubleAdd_bits_correct : 
    forall bs e,
    groupMul_doubleAdd_bits bs e == groupMul (natFromBits bs) e.

    induction bs; intuition; simpl in *.
    reflexivity.
    destruct a.
    rewrite PeanoNat.Nat.add_0_r.
    rewrite groupMul_distr.
    simpl.
    rewrite (groupAdd_comm _ idElem).
    rewrite groupAdd_id.
    rewrite IHbs.
    rewrite groupDouble_correct.
    rewrite groupMul_distr.
    reflexivity.
    
    simpl.
    rewrite PeanoNat.Nat.add_0_r.
    rewrite groupMul_distr.
    rewrite IHbs.
    rewrite groupDouble_correct.
    reflexivity.

  Qed.


  (* a simple n-bit window*)
  Definition Window := list bool.

  Definition groupAdd_window w e1 e2 :=
    (groupAdd (groupMul_doubleAdd_bits w e1) e2).

  Fixpoint groupMul_windows (ws : list Window)(e : GroupElem) :=
    match ws with
    | nil => idElem
    | w :: ws' => (groupAdd_window w e (groupDouble_n (length w) (groupMul_windows ws' e)))
    end.

  Theorem groupMul_doubleAdd_bits_app : forall ls1 ls2 e,
    groupMul_doubleAdd_bits (ls1 ++ ls2) e == 
    groupAdd (groupMul_doubleAdd_bits ls1 e) (groupDouble_n (length ls1) (groupMul_doubleAdd_bits ls2 e)).

    induction ls1; intuition; simpl in *.
    rewrite groupAdd_id.
    reflexivity.
    destruct a.
    rewrite IHls1.
    rewrite groupAdd_assoc.
    apply groupAdd_proper.
    reflexivity.
    rewrite <- groupDouble_distrib.
    reflexivity.
    
    rewrite IHls1.
    rewrite <- groupDouble_distrib.
    reflexivity.
  Qed.

  Theorem groupMul_windows_correct_h : forall ws e,
    (groupMul_windows ws e) == (groupMul_doubleAdd_bits (flatten ws) e).

    induction ws; intuition; simpl in *.  
    reflexivity.
    unfold groupAdd_window.
    rewrite groupMul_doubleAdd_bits_app.
    apply groupAdd_proper.
    reflexivity.
    eapply groupDouble_n_equiv_compat.
    eauto.

  Qed.

  Theorem groupMul_windows_correct : forall ws e,
    (groupMul_windows ws e) == (groupMul (natFromBits (flatten ws)) e).

    intros.
    rewrite groupMul_windows_correct_h.
    apply groupMul_doubleAdd_bits_correct.

  Qed.

  (* Signed windows *)
  Local Open Scope Z_scope.

  Theorem groupMul_doubleAdd_pos_succ : forall p e,
    groupMul_doubleAdd_pos (Pos.succ p) e ==
    groupAdd e (groupMul_doubleAdd_pos p e).

    induction p; intuition; simpl in *.
    rewrite IHp.
    repeat rewrite groupDouble_correct.
    rewrite groupAdd_assoc.
    apply groupAdd_proper.
    reflexivity.
    rewrite groupAdd_comm.
    rewrite groupAdd_assoc.
    reflexivity.
    reflexivity.
    apply groupDouble_correct.

  Qed.

  Definition groupMul_doubleAdd_signed (s : Z)(e : GroupElem) :=
    match s with
    | Z0 => idElem
    | Zpos p => groupMul_doubleAdd_pos p e 
    | Zneg p => groupInverse (groupMul_doubleAdd_pos p e)
    end.

  Theorem groupMul_signed_correct : forall n e,
    groupMul_doubleAdd_signed (Z.of_nat n) e == groupMul n e.

    intros.
    remember (Z.of_nat n) as z. 
    destruct z; simpl.
    symmetry in Heqz.
    apply Z_of_nat_0_if in Heqz.
    subst.
    reflexivity.

    rewrite groupMul_doubleAdd_pos_equiv.
    rewrite <- Znat.positive_nat_Z in Heqz.
    rewrite Znat.Nat2Z.inj_iff in Heqz.
    subst.
    reflexivity.

    lia.
  
  Qed.

  Variable wsize : nat.
  Hypothesis wsize_nz : wsize <> 0%nat.


  (* Use an abstract procedure for computing a multiple of a particular element. 
      This can be instantiated with a table lookup.
  *)
  Section SignedWindows.
  Variable p : GroupElem.
  Variable RegularWindow : SignedWindow -> Prop.
  Variable bMultiple : SignedWindow -> GroupElem.
  Hypothesis bMultiple_correct : forall w, 
    RegularWindow w ->
    bMultiple w == groupMul_doubleAdd_signed w p.
  
  Definition groupAdd_signedWindow w e2 :=
    (groupAdd (bMultiple w) e2).

  Fixpoint groupMul_signedWindows (ws : list SignedWindow) :=
    match ws with
    | nil => idElem
    | w :: ws' => 
      (groupAdd_signedWindow w 
        (groupDouble_n wsize (groupMul_signedWindows ws')))
    end.


  (* a form of the group multiplication using fold that looks more like the implementation. *)
  Fixpoint groupMul_signedWindows_h e (ws : list SignedWindow) :=
    match ws with
    | nil => e
    | w :: ws' => 
      (groupAdd_signedWindow w 
        (groupDouble_n wsize (groupMul_signedWindows_h e ws')))
    end.

  Definition groupMul_signedWindows_fold_body p w :=
    (groupAdd_signedWindow w (groupDouble_n wsize p)).

  Theorem groupMul_signedWindows_h_fold_equiv : forall ws e,
    (groupMul_signedWindows_h e ws) = (fold_left groupMul_signedWindows_fold_body (rev ws) e).

    induction ws; intuition idtac; simpl.
    rewrite fold_left_app.
    simpl.
    unfold groupMul_signedWindows_fold_body.
    f_equal.
    f_equal.
    apply IHws.
  Qed.

  Theorem groupMul_signedWindows_h_equiv : forall ws,
    groupMul_signedWindows_h idElem ws = groupMul_signedWindows ws.

    induction ws; intuition idtac; simpl in *.
    rewrite IHws.
    reflexivity.

  Qed.

  Theorem groupMul_signedWindows_fold_equiv : forall ws,
    (groupMul_signedWindows ws) = (fold_left groupMul_signedWindows_fold_body (rev ws) idElem).

    intros.
    rewrite <- groupMul_signedWindows_h_fold_equiv.
    rewrite groupMul_signedWindows_h_equiv.
    reflexivity.
  Qed.

  (* end fold multiplication model *)

  Fixpoint windowsToZ (ws : list Z) :=
    match ws with
    | nil => 0
    | w :: ws' => (w + (zDouble_n wsize (windowsToZ ws')))
    end.

  Theorem groupMul_pos_distr : forall a b e,
    groupMul_doubleAdd_pos (a + b) e == 
    groupAdd (groupMul_doubleAdd_pos a e) (groupMul_doubleAdd_pos b e).

    induction a; intros; simpl in *.
    
    +destruct b; simpl.
    rewrite Pos.add_carry_spec.
    rewrite groupMul_doubleAdd_pos_succ.
    rewrite IHa.
    rewrite groupDouble_distrib.
    rewrite groupDouble_correct.
    repeat rewrite groupAdd_assoc.
    apply groupAdd_proper.
    reflexivity.
    rewrite (groupAdd_comm (groupDouble (groupMul_doubleAdd_pos a e))).
    rewrite groupAdd_assoc.
    apply groupAdd_proper.
    reflexivity.
    rewrite groupDouble_distrib.
    rewrite groupAdd_comm.
    reflexivity.

    rewrite IHa.
    rewrite groupAdd_assoc.
    apply groupAdd_proper.
    reflexivity.
    rewrite groupDouble_distrib.
    reflexivity.

    rewrite groupMul_doubleAdd_pos_succ.
    rewrite groupDouble_distrib.
    repeat rewrite groupDouble_correct.
    repeat rewrite groupAdd_assoc.
    apply groupAdd_proper.
    reflexivity.
    symmetry.
    rewrite (groupAdd_comm (groupMul_doubleAdd_pos a e)).
    rewrite groupAdd_assoc.
    rewrite (groupAdd_comm (groupMul_doubleAdd_pos a e)).
    rewrite groupAdd_assoc.
    reflexivity.

    + destruct b; simpl.
    rewrite IHa.  
    rewrite (groupAdd_comm (groupDouble (groupMul_doubleAdd_pos a e))).
    rewrite groupAdd_assoc.
    apply groupAdd_proper.
    reflexivity.
    rewrite groupDouble_distrib.
    rewrite groupAdd_comm.
    reflexivity.
  
    rewrite IHa.
    rewrite groupDouble_distrib.
    reflexivity.

    apply groupAdd_comm.

    + destruct b; simpl.
    rewrite groupMul_doubleAdd_pos_succ.
    rewrite groupDouble_distrib.
    rewrite groupDouble_correct.
    repeat rewrite groupAdd_assoc.
    reflexivity.

    reflexivity.
  
    apply groupDouble_correct.

  Qed.


  Theorem groupMul_pos_sub_distr : forall p1 p2 e,
    (p2 < p1)%positive ->
    groupMul_doubleAdd_pos (p1 - p2) e == groupAdd (groupMul_doubleAdd_pos p1 e) (groupInverse (groupMul_doubleAdd_pos p2 e)).

    intros.
    unfold BinPosDef.Pos.sub.
    apply Pos.sub_mask_pos in H.
    destruct H.
    rewrite H.
    rewrite Pos.sub_mask_pos_iff in H.
    subst.
    rewrite groupMul_pos_distr.
    rewrite (groupAdd_comm (groupMul_doubleAdd_pos p2 e)).
    rewrite groupAdd_assoc.
    rewrite groupInverse_correct.
    rewrite groupAdd_comm.
    rewrite groupAdd_id.
    reflexivity.
  
  Qed.


  Theorem groupMul_signed_pos_sub_distr : forall p1 p2 e,
    groupMul_doubleAdd_signed (Z.pos_sub p1 p2) e == groupAdd (groupMul_doubleAdd_pos p1 e) (groupInverse (groupMul_doubleAdd_pos p2 e)).

    intros.
    rewrite Z.pos_sub_spec.
    case_eq (p1 ?= p2)%positive; intros; simpl.
    + rewrite Pos.compare_eq_iff in H. subst.
    rewrite groupInverse_correct.
    reflexivity.

    + rewrite groupMul_pos_sub_distr.
    rewrite groupInverse_add_distr.
    rewrite groupInverse_involutive.
    apply groupAdd_comm.
    rewrite Pos.compare_lt_iff in H.
    trivial.

    + apply groupMul_pos_sub_distr.
    rewrite Pos.compare_gt_iff in H.
    trivial.

  Qed.

  Theorem groupMul_signed_distr : forall a b e,
    groupMul_doubleAdd_signed (a + b) e == 
    groupAdd (groupMul_doubleAdd_signed a e) (groupMul_doubleAdd_signed b e).

    intuition.
    destruct a; simpl.
    + rewrite groupAdd_id. reflexivity.

    + destruct b; simpl.
    rewrite groupAdd_comm.
    rewrite groupAdd_id. reflexivity.

    apply groupMul_pos_distr.
    apply groupMul_signed_pos_sub_distr.

    + destruct b; simpl.
    rewrite groupAdd_comm.
    rewrite groupAdd_id.
    reflexivity.

    rewrite groupMul_signed_pos_sub_distr.
    apply groupAdd_comm.
    rewrite groupMul_pos_distr.
    rewrite groupInverse_add_distr.
    reflexivity.
    
  Qed.

  Theorem zDouble_n_mul : forall n x e,
    groupMul_doubleAdd_signed (zDouble_n n x) e == groupDouble_n n (groupMul_doubleAdd_signed x e).

    induction n; intuition; simpl in *.
    rewrite zDouble_n_0.
    reflexivity.

    rewrite <- IHn.
    rewrite zDouble_n_S.
    rewrite groupDouble_correct.
    rewrite Z_double_sum.
    rewrite groupMul_signed_distr.
    reflexivity.
    
  Qed.

  Theorem groupMul_signedWindows_correct : 
    forall ws,
    Forall RegularWindow ws ->
    groupMul_signedWindows ws == groupMul_doubleAdd_signed (windowsToZ ws) p.

    induction ws; intuition; simpl in *.
    reflexivity.

    inversion H; clear H; subst.
    rewrite groupMul_signed_distr.
    unfold groupAdd_signedWindow.
    
    apply groupAdd_proper.
    eapply bMultiple_correct.
    eauto.
    transitivity (groupDouble_n wsize (groupMul_doubleAdd_signed (windowsToZ ws) p)).
    eapply groupDouble_n_equiv_compat.
    eauto.
    rewrite zDouble_n_mul.
    reflexivity.

  Qed.

  End SignedWindows.

  (* signed odd windows *)
  Section SignedOddWindows.
  
  Definition OddWindow w := Z.odd w = true /\ Z.abs w < Z.shiftl 1 (Z.of_nat wsize).
  Variable p : GroupElem.
  (* Definitions n this section abstract over a function pMultiple that takes a signed window w and 
  returns w * p. In practice, this function is implemented using a table lookup, but the abstraction allows
  us to simplify and generalize the proof of correctness of the larger group multiplication operation. A later
  proof will show that this group multiplication is correct with pMultiple is instantiated with a partfcular
  table lookup operation. *)
  Variable pMultiple : SignedWindow -> GroupElem.
  Hypothesis pMultiple_correct : forall w,
    OddWindow w ->
    pMultiple w == groupMul_doubleAdd_signed w p.

  (* The group multiplication function based on signed regular windows takes an odd number n
  encoded into signed windows and a boolean which determines whether the desired product is 
  n * p or (n - 1) * p. *)
  Definition groupMul_signedRegularWindows (isEven : bool) ws :=
    if isEven 
      then (groupAdd (groupMul_signedWindows pMultiple ws) (groupInverse p))
      else (groupMul_signedWindows pMultiple ws).

  Definition RegularWindows (ws : list Z) :=
    forall w, In w ws -> OddWindow w.

  Definition RegularReprOfZ (ws : list Z)(z : Z) :=
    RegularWindows ws /\
    if (Z.odd z)
      then (windowsToZ ws) = z
      else (windowsToZ ws) = (Z.succ z).

  Theorem windowsToZ_app : forall ws z,
    windowsToZ (ws ++ z::nil) = (windowsToZ ws) + (zDouble_n ((length ws) * wsize) z).

    induction ws; intuition eauto; simpl in *.
    rewrite zDouble_n_0.
    rewrite zDouble_n_0_r.
    lia.

    rewrite IHws.
    rewrite <- Z.add_assoc.
    f_equal.
    repeat rewrite zDouble_n_sum.
    rewrite zDouble_add_distr.
    reflexivity.

  Qed.

  Theorem windowsToZ_bit_length_small : forall ws,
    (forall w, In w ws -> Z.abs w < Z.shiftl 1 (Z.of_nat wsize)) ->
    Z.abs (windowsToZ ws) < (zDouble_n (length ws * wsize) 1).

    induction ws; intros; simpl in *.
    rewrite zDouble_n_0.
    lia.
    rewrite zDouble_n_sum.
    eapply Z.le_lt_trans.
    apply Z.abs_triangle.

    eapply Z.lt_le_trans.
    apply Zorder.Zplus_lt_compat_r.
    eapply H.
    intuition eauto.
    unfold zDouble_n.
    repeat rewrite Z.shiftl_mul_pow2.
    rewrite Z.abs_mul.
    rewrite (Z.abs_eq (2 ^ Z.of_nat wsize)).
    rewrite <- Z.mul_add_distr_r.
    rewrite Z.mul_1_l.
    apply Z.mul_le_mono_nonneg_r.
    apply Z.pow_nonneg.
    lia.
    assert (Z.abs (windowsToZ ws) < 2 ^ Z.of_nat (length ws * wsize)).
    eapply Z.lt_le_trans.
    eapply IHws.
    eauto.
    unfold zDouble_n. 
    rewrite Z.shiftl_mul_pow2.
    rewrite Z.mul_1_l.
    reflexivity.
    lia.
    lia.
    apply Z.pow_nonneg.
    lia.
    lia.
    lia.
    lia.
    lia.
 
  Qed.

  Theorem windowsToZ_highWindowNonNeg : forall ws,
    RegularWindows ws ->
    0 <= (windowsToZ ws) ->
    0 <= last ws 0.

    induction ws using rev_ind; intuition; simpl in *.
    rewrite windowsToZ_app in *.
    rewrite last_last.
    assert ( 0 <= (zDouble_n (length ws * wsize) x)).
    assert ((Z.abs (windowsToZ ws)) < Z.abs (zDouble_n (length ws * wsize) x)).
    eapply Z.lt_le_trans.
    apply windowsToZ_bit_length_small.
    intros.
    unfold RegularWindows, OddWindow in *.
    apply H.
    eapply in_or_app.
    intuition eauto.

    destruct x.
  
    (* contradiction: 0 is not odd *)
    + assert (false = true).
    unfold RegularWindows, OddWindow in *.
    specialize (H 0).
    simpl in *.
    eapply H.
    eapply in_or_app.
    simpl.
    intuition eauto.
    discriminate.

    (* positive case *)
    + rewrite Z.abs_eq.
    unfold zDouble_n.
    repeat rewrite Z.shiftl_mul_pow2.
    apply Z.mul_le_mono_nonneg_r.
    apply Z.pow_nonneg.
    lia.
    lia.
    lia.
    lia.
    apply Z.shiftl_nonneg.
    lia.

    (* negative case *)
    +
    rewrite Z.abs_neq.
    rewrite zDouble_n_opp.
    rewrite Pos2Z.opp_neg.
    unfold zDouble_n.
    repeat rewrite Z.shiftl_mul_pow2.
    apply Z.mul_le_mono_nonneg_r.
    apply Z.pow_nonneg.
    lia.
    lia.
    lia.
    lia.
    unfold zDouble_n.
    repeat rewrite Z.shiftl_mul_pow2.
    apply Z.mul_nonpos_nonneg.
    lia.
    apply Z.pow_nonneg.
    lia.
    lia.

    + lia.
    + eapply Z.shiftl_nonneg.
    eauto.
    
  Qed.

  (* In any regular representation of a non-negative number, the last window is non-negative.
    This fact is used by implementations to skip the sign check on the last window. *)
  Theorem RegularReprOfZ_highWindowNonNeg : forall ws z,
    RegularReprOfZ ws z ->
    0 <= z ->
    0 <= last ws 0.

    unfold RegularReprOfZ in *; intuition eauto.
    case_eq (Z.odd z); intros.
    rewrite H in H2. subst.
    apply windowsToZ_highWindowNonNeg; eauto.

    rewrite H in H2.
    eapply windowsToZ_highWindowNonNeg.
    eauto.
    rewrite H2.
    eapply Z.le_trans.
    eapply H0.
    lia.

  Qed.

  Theorem groupMul_signedRegularWindows_correct_h : forall ws z,
    RegularReprOfZ ws z ->
    groupMul_signedRegularWindows (Z.even z) ws == groupMul_doubleAdd_signed z p.

    unfold groupMul_signedRegularWindows, RegularReprOfZ in *; intuition.
    rewrite Zeven.Zeven_odd_bool.
    case_eq (Z.odd z); simpl; intros;
    rewrite H in H1; subst;
    rewrite groupMul_signedWindows_correct; trivial.
    reflexivity.

    eapply pMultiple_correct.
    unfold RegularWindows in *.
    eapply Forall_forall.
    eauto.

    rewrite H1.
    rewrite <- Z.add_1_l.
    rewrite groupMul_signed_distr.
    simpl.
    rewrite (groupAdd_comm p).
    rewrite groupAdd_assoc.
    rewrite groupInverse_correct.
    rewrite groupAdd_comm.
    rewrite groupAdd_id.
    reflexivity.

    eauto.
    eapply Forall_forall.
    eauto.

  Qed.

  Definition RegularReprOfNat ws n :=
    RegularReprOfZ ws (Z.of_nat n).

  Theorem groupMul_signedRegularWindows_correct : forall ws n,
    RegularReprOfNat ws n ->
    groupMul_signedRegularWindows (even n) ws == groupMul n p.

    unfold RegularReprOfNat in *; intros.
    rewrite even_of_nat_equiv.
    rewrite groupMul_signedRegularWindows_correct_h.
    apply groupMul_signed_correct.
    trivial.

  Qed.

  (* recoding *)

  Definition RegularReprOfOddZ (ws : list Z)(z : Z) :=
    RegularWindows ws /\
    (windowsToZ ws) = z.

  Definition twoToWsize := Z.shiftl 1 (Z.of_nat wsize).
  Definition wsize_mask := Z.sub (Z.shiftl twoToWsize 1) 1.

  Fixpoint recode_rwnaf_odd (nw : nat)(n : Z) :=
    match nw with
    | 0%nat => n :: nil
    | S nw' =>
      let k_i := (n mod (Z.double twoToWsize)) - twoToWsize in
      let n' := (n - k_i) / twoToWsize in
      k_i :: (recode_rwnaf_odd nw' n')
    end.

  Theorem recode_rwnaf_odd_length : forall nw z,
    List.length (recode_rwnaf_odd nw z) = (S nw).

    induction nw; intros; simpl in *; trivial.
    rewrite IHnw.
    trivial.

  Qed.

  Theorem twoToWsize_pos : 
    0 < twoToWsize.

    intros.
    unfold twoToWsize.
    rewrite Z.shiftl_mul_pow2.
    apply Z.mul_pos_pos.
    lia.
    apply Z.pow_pos_nonneg.
    lia.
    lia.
    lia.
  Qed.

  Theorem twoToWsize_mod_2 :
    twoToWsize mod 2 = 0.

    intuition.
    unfold twoToWsize.
    rewrite Z.shiftl_1_l.
    apply pow_mod_0.
    intuition.

  Qed.

  Theorem zDouble_n_wsize : forall x,
    zDouble_n wsize x = twoToWsize * x.

    intuition.
    unfold zDouble_n, twoToWsize.
    repeat rewrite Z.shiftl_mul_pow2;
    lia.
  Qed.

  Theorem recodeWindows_rwnaf_odd_correct : forall nw z,
    Z.odd z = true ->
    0 <= z ->
    z < (Z.shiftl 1 (Z.of_nat ((S nw) * wsize))) ->
    RegularReprOfOddZ (recode_rwnaf_odd nw z) z.

    induction nw; intuition idtac; simpl in *.

    assert (twoToWsize >  0).
    eapply shiftl_pos.
    lia.
    lia.

    unfold RegularReprOfOddZ, RegularWindows; intuition; simpl in*; intuition; subst; trivial.
    unfold OddWindow.
    rewrite Zdiv.Zodd_mod.
    intuition.
    apply Zbool.Zeq_is_eq_bool.
    rewrite Zdiv.Zodd_mod in H.
    apply Zbool.Zeq_is_eq_bool in H.
    trivial.
    rewrite Z.abs_eq.
    rewrite plus_0_r in H1.
    trivial.
    trivial.
    rewrite zDouble_n_id.
    lia.
 
    assert (twoToWsize >  0).
    apply shiftl_pos. lia. lia.

    assert (Z.odd ((z - (z mod Z.double twoToWsize - twoToWsize)) / twoToWsize) = true).
    rewrite Zdiv.Zodd_mod.
    apply Zbool.Zeq_is_eq_bool.
    rewrite Z.sub_sub_distr.
    rewrite mod_div_prod.
    rewrite <- Z.add_mod_idemp_l.
    rewrite Z.double_spec.
    rewrite Zdiv.Zminus_mod_idemp_r.
    rewrite Z.sub_diag.
    rewrite Zdiv.Zmod_0_l.
    rewrite Z.add_0_l.
    rewrite Z.mod_small.  
    apply Zdiv.Z_div_same.
    trivial.
    intuition idtac.
    lia.
    lia.
    lia.
    lia.
    lia.

    assert (0 <= (z - (z mod Z.double twoToWsize - twoToWsize)) / twoToWsize).
    apply Zdiv.Z_div_pos.
    lia.
    rewrite Z.sub_sub_distr.
    apply Z.add_nonneg_nonneg.
    apply Z.le_0_sub.
    apply Z.mod_le; trivial.
    rewrite Z_double_sum.
    lia.
    lia.

    assert ((z - (z mod Z.double twoToWsize - twoToWsize)) / twoToWsize < Z.shiftl 1 (Z.of_nat (wsize + nw * wsize))).
    assert ((z - (z mod Z.double twoToWsize - twoToWsize)) < Z.shiftl 1 (Z.of_nat (wsize + (wsize + nw * wsize)))).
    rewrite Z.sub_sub_distr.
    assert (z - z mod Z.double twoToWsize <= Z.shiftl 1 (Z.of_nat (wsize + (wsize + nw * wsize))) - Z.double twoToWsize).
    eapply mod_clear_lt.
    rewrite Z_double_sum.
    lia.  
    unfold twoToWsize.  
    rewrite Zdouble_shiftl.
    apply Zshiftl_divide.   
    lia.
    lia.
    lia.
    lia.
    lia.
    rewrite Z_double_sum in *.
    lia.
 
    replace (Z.shiftl 1 (Z.of_nat (wsize + nw * wsize))) with  ((Z.shiftl 1 (Z.of_nat (wsize + (wsize + nw * wsize)))) / twoToWsize).
    apply Zdiv_lt_compat.
    unfold twoToWsize.
    apply Zshiftl_divide.
    lia.
    lia.
    lia.
    lia.
    trivial.
    unfold twoToWsize.
    rewrite (Z.shiftl_mul_pow2 _ (Z.of_nat wsize)).
    repeat rewrite Z.mul_1_l.
    rewrite <- Z.shiftr_div_pow2.
    rewrite Z.shiftr_shiftl_l.
    f_equal.
    lia.
    lia.
    lia.
    lia.

    specialize (IHnw ((z - (z mod Z.double twoToWsize - twoToWsize)) / twoToWsize)); intuition idtac. 
 
    unfold RegularReprOfOddZ, RegularWindows in *; simpl in *; intuition; subst.
    unfold OddWindow.
    rewrite Zdiv.Zodd_mod.
    intuition.
    apply Zbool.Zeq_is_eq_bool.
    rewrite <- Zdiv.Zminus_mod_idemp_r.
    rewrite twoToWsize_mod_2.
    rewrite Z.sub_0_r.
    rewrite Zmod_mod_gen.
    apply Zbool.Zeq_is_eq_bool.
    rewrite <- Zdiv.Zodd_mod.
    trivial.
    rewrite Z_double_sum.
    lia.
    lia.
    rewrite Z.double_spec.
    rewrite Z.mul_comm.
    apply Zdiv.Z_mod_mult.

    (* prove that window is small*)
    apply Z.abs_lt.
    intuition eauto.
    unfold twoToWsize in *.
    assert (z mod Z.double (Z.shiftl 1 (Z.of_nat wsize)) > 0).
    assert (0 <= z mod Z.double (Z.shiftl 1 (Z.of_nat wsize))).
    apply Zdiv.Z_mod_lt.
    assert (Z.shiftl 1 (Z.of_nat wsize) > 0).
    apply shiftl_pos.
    lia.
    lia.
    rewrite Z_double_sum.
    lia.
    assert (z mod Z.double (Z.shiftl 1 (Z.of_nat wsize)) <> 0).
    rewrite Z.double_spec.
    rewrite Z.rem_mul_r.
    rewrite Zdiv.Zmod_odd.
    rewrite H.
    lia.
    lia.
    apply Z.gt_lt.
    apply shiftl_pos.
    lia.
    lia.
    lia.
    lia.

    unfold twoToWsize in *.
    assert (z mod Z.double (Z.shiftl 1 (Z.of_nat wsize)) < 2*(Z.shiftl 1 (Z.of_nat wsize))).
    apply Zdiv.Z_mod_lt.
    assert (Z.shiftl 1 (Z.of_nat wsize) > 0).
    apply shiftl_pos.
    lia.
    lia.
    lia.
    lia.

    rewrite H8.
    clear H8.

    rewrite zDouble_n_wsize.
    rewrite <- Zdiv.Z_div_exact_2.
    lia.
    trivial.
    
    rewrite Z.sub_sub_distr.
    rewrite <- Zdiv.Zplus_mod_idemp_r.
    rewrite Zdiv.Z_mod_same_full.
    rewrite Z.add_0_r.
    rewrite <- Zdiv.Zminus_mod_idemp_r.
    rewrite Zmod_mod_gen.
    rewrite <- Zdiv.Zminus_mod_idemp_l.
    rewrite Z.sub_diag.
    apply Zdiv.Zmod_0_l.
    rewrite Z_double_sum.
    lia.
    lia.
    rewrite Z.double_spec.
    apply Zdiv.Z_mod_mult.

  Qed.

  Variable numWindows : nat.
  Hypothesis numWindows_nz : numWindows <> 0%nat.

  Definition recode_rwnaf z :=
    recode_rwnaf_odd (pred numWindows) (Z.lor z 1).

  Theorem RegularReprOfZ_odd : forall ws z,
    Z.odd z = true ->
    RegularReprOfOddZ ws z ->
    RegularReprOfZ ws z.

    unfold RegularReprOfOddZ, RegularReprOfZ; intuition.
    rewrite H; trivial.

  Qed.

  Theorem RegularReprOfZ_succ : forall ws z,
    Z.even z = true ->
    RegularReprOfOddZ ws (Z.succ z) ->
    RegularReprOfZ ws z.

    unfold RegularReprOfOddZ, RegularReprOfZ; intuition.
    rewrite <- Z.negb_even.
    rewrite H.
    trivial.

  Qed.

  Theorem recode_rwnaf_correct : forall n,
    (Z.of_nat n) < (Z.shiftl 1 (Z.of_nat (numWindows * wsize))) ->
    RegularReprOfNat (recode_rwnaf (Z.of_nat n)) n.

    intuition.
    unfold recode_rwnaf.
    case_eq (Z.odd (Z.of_nat n)); intros.
    rewrite Z_odd_lor_1; trivial.
    eapply RegularReprOfZ_odd; trivial.
    eapply recodeWindows_rwnaf_odd_correct; eauto.
    lia.
    rewrite Nat.succ_pred_pos; lia.

    rewrite Z_even_lor_1.
    eapply RegularReprOfZ_succ.
    rewrite <- Z.negb_odd.
    rewrite H0.
    trivial.
    eapply recodeWindows_rwnaf_odd_correct; eauto.
    rewrite Z.odd_succ.
    rewrite <- Z.negb_odd.
    rewrite H0.
    trivial.
    lia.
    apply Z_even_lt.
    rewrite <- Z.negb_odd.
    rewrite H0.
    trivial.
    rewrite Z.shiftl_mul_pow2.
    rewrite Z.mul_1_l.
    rewrite Z.even_pow.
    trivial.
    lia.
    lia.
    trivial.
    rewrite Nat.succ_pred_pos; lia.
    rewrite <- Z.negb_odd.
    rewrite H0.
    trivial.

  Qed.

  Theorem recode_rwnaf_length : forall z,
    List.length (recode_rwnaf z) = numWindows.

    intros.
    unfold recode_rwnaf.
    rewrite recode_rwnaf_odd_length.
    lia.

  Qed.

  Theorem recode_rwnaf_bound_In : forall x z,
    (BinInt.Z.of_nat x < BinInt.Z.shiftl 1 (BinInt.Z.of_nat (numWindows * wsize)))%Z ->
    List.In z (recode_rwnaf (Z.of_nat x)) ->
    (-2^(Z.of_nat wsize) < z < (2^(Z.of_nat wsize)))%Z.

    intros.
    apply Z.abs_lt.
    rewrite <- Z.shiftl_1_l.
    eapply recode_rwnaf_correct; eauto.

  Qed.

  Theorem recode_rwnaf_bound_nth : forall n x,
    (BinInt.Z.of_nat x < BinInt.Z.shiftl 1 (BinInt.Z.of_nat (numWindows * wsize)))%Z ->
    (-2^(Z.of_nat wsize) < (List.nth n
   (recode_rwnaf (Z.of_nat x)) 0) < (2^(Z.of_nat wsize)))%Z.

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

  Definition groupMul_signedRegular n :=
    groupMul_signedRegularWindows (even n) (recode_rwnaf (Z.of_nat n)).

  Theorem groupMul_signedRegular_correct : forall n,
    Z.of_nat n < Z.shiftl 1 (Z.of_nat (numWindows * wsize)) ->
    groupMul_signedRegular n == groupMul n p.

    intros.
    unfold groupMul_signedRegular.
    apply groupMul_signedRegularWindows_correct.
    apply recode_rwnaf_correct.
    trivial.
  Qed.

  Theorem recode_rwnaf_last_nonneg : forall n,
    Z.of_nat n < Z.shiftl 1 (Z.of_nat (numWindows * wsize)) ->
    0 <= last (recode_rwnaf (Z.of_nat n)) 0.
    
    intros.
    eapply RegularReprOfZ_highWindowNonNeg.
    eapply recode_rwnaf_correct.
    trivial.
    lia.
  Qed.

  End SignedOddWindows.

  (* precomputation and table lookup with signed integers *)
  Definition tableSize : nat := shiftl 1 (wsize - 1).
  
  Definition preCompTable_h n ls e :=
    fold_left (fun ls _ => ls ++ (groupAdd e (last ls idElem))::nil) (forNats n) ls.

  Definition preCompTable x := preCompTable_h (pred tableSize) (x::nil) (groupDouble x).

  Theorem tableSize_correct : forall x, 
      List.length (preCompTable x)  = tableSize.

    intros.
    unfold preCompTable, preCompTable_h.
    rewrite fold_app_length.
    rewrite forNats_length.
    simpl.
    unfold tableSize.
    destruct wsize; try lia; simpl.
    repeat rewrite Nat.sub_0_r.
    assert (0 < shiftl 1 n)%nat.
    apply nat_shiftl_nz.
    lia.
    lia.

  Qed.

  Theorem preCompTable_h_nth : forall n2 n1 ls e x,
    (0 < length ls)%nat -> 
    (n1 < n2 + (length ls))%nat ->
    (forall n, (n < length ls)%nat -> nth n ls idElem == groupAdd (groupMul n e) x) ->
    nth n1 (preCompTable_h n2 ls e) idElem == groupAdd (groupMul n1 e) x.

    unfold preCompTable_h in *.
    induction n2; intuition; simpl in *.
    erewrite IHn2.
    reflexivity.
    rewrite app_length.
    simpl.
    lia.
    rewrite app_length.
    simpl.
    lia.
    intros.
    destruct (lt_dec n (length ls)).
    rewrite app_nth1; eauto.
    rewrite app_length in H2. simpl in *.
    assert (n = length ls).
    lia.
    subst.
    rewrite app_nth2.
    rewrite minus_diag.
    simpl.
    rewrite last_nth_equiv.
    rewrite H1.
    destruct ls; simpl in *.
    intuition.
    rewrite groupAdd_assoc.
    reflexivity.
    destruct ls; simpl in *; lia.
    lia.

  Qed.

  Theorem preCompTable_nth : forall n x,
    (n < tableSize)%nat -> 
    nth n (preCompTable x) idElem == groupMul (2 * n + 1) x.

    intuition.
    unfold preCompTable.
    rewrite (preCompTable_h_nth _ _ _ x).
    rewrite groupMul_distr.
    simpl.
    rewrite (groupAdd_comm _ idElem).
    rewrite groupAdd_id.
    apply groupAdd_proper.
    rewrite plus_0_r.
    rewrite groupDouble_correct.
    rewrite groupMul_distr.
    rewrite groupMul_groupAdd_distr.
    reflexivity.  
    reflexivity.

    simpl.
    lia.
    simpl in *.
    assert ( 1 <> 0)%nat by lia.
    assert (tableSize <> O).
    intuition idtac.
    eapply H0.
    eapply Nat.shiftl_eq_0_iff.
    eauto.
    lia.

    intros.
    simpl in *.
    destruct n0; simpl in *.
    rewrite groupAdd_id.
    reflexivity.
    lia.
    
  Qed.

  Definition groupMul_signed_table (t : list GroupElem) x :=
    let abs_x := (Z.abs x) in
    let e := nth (Z.to_nat (Z.shiftr abs_x 1)) t idElem in 
    if (Z.ltb x 0) then (groupInverse e) else e.

  Definition PreCompTable_for_elem t e :=
    forall x, 
      Z.odd (Z.pos x) = true ->
      (Z.to_nat (Z.shiftr (Z.pos x) 1) < tableSize)%nat ->
      nth (Z.to_nat (Z.shiftr (Z.pos x) 1)) t idElem == groupMul_doubleAdd_pos x e.

  Theorem preCompTable_correct : forall x,
    PreCompTable_for_elem (preCompTable x) x.

    intros.
    unfold PreCompTable_for_elem. intros.
    rewrite groupMul_doubleAdd_pos_equiv.
    rewrite preCompTable_nth.
    rewrite Nat.mul_comm.
    replace 2%nat with (Z.to_nat 2).
    rewrite <- Znat.Z2Nat.inj_mul.
    replace 2 with (2^1).
    rewrite <- Z.shiftl_mul_pow2.
    rewrite <- Z.ldiff_ones_r.
    rewrite Z_ldiff_1_odd_sub.
    replace 1%nat with (Z.to_nat 1).
    rewrite <- Znat.Z2Nat.inj_add.
    rewrite Z.sub_add.
    simpl.
    reflexivity.

    lia.
    lia.
    lia.
    trivial.
    lia.
    lia.
    apply Z.pow_1_r.
    eapply Z.shiftr_nonneg.
    lia.
    lia.
    lia.

    trivial.

  Qed.

  Theorem shiftr_window_small : forall p,
    Z.pos p < Z.shiftl 1 (Z.of_nat wsize) ->
    (Z.to_nat (Z.shiftr (Z.pos p) 1) < tableSize)%nat.

    intros.
    unfold tableSize.
    replace 1 with (Z.of_nat 1).
    rewrite shiftr_to_nat_eq.
    eapply (@lt_if_shiftl_lt 1).
    eapply Nat.le_lt_trans.
    eapply shiftl_shiftr_le.
    replace (shiftl (shiftl 1 (wsize - 1)) 1) with (shiftl 1 wsize).
    replace (shiftl 1 wsize) with (Z.to_nat (Z.shiftl 1 (Z.of_nat wsize))).
    eapply Znat.Z2Nat.inj_lt.
    apply Pos2Z.pos_is_nonneg.
    eapply Z.shiftl_nonneg.
    apply Pos2Z.pos_is_nonneg.
    trivial.
    rewrite shiftl_to_nat_eq.
    trivial.
    destruct wsize. intuition. simpl.
    rewrite Nat.sub_0_r.
    trivial.
    lia.
    lia.

  Qed.

  Theorem shiftr_window_small_Z : forall z,
    0 <= z < Z.shiftl 1 (Z.of_nat wsize) ->
    (Z.to_nat (Z.shiftr z 1) < tableSize)%nat.

    intros.
    destruct z.
    unfold tableSize.
    simpl.
    apply nat_shiftl_nz.
    lia.

    apply shiftr_window_small; intuition idtac.

    lia.
  Qed.

  Theorem signedMul_table_correct : forall e (t : list GroupElem) x,
    OddWindow x ->
    PreCompTable_for_elem t e ->
    groupMul_signed_table t x == groupMul_doubleAdd_signed x e.

    intros. unfold OddWindow in *; intuition.
    unfold groupMul_signed_table, groupMul_doubleAdd_signed.
    destruct x.
    simpl in *. discriminate.

    simpl in *.
    eapply H0.
    simpl.
    trivial.
    apply shiftr_window_small; eauto.

    simpl in *.
    apply groupInverse_proper.
    eapply H0.
    simpl.
    trivial.
    apply shiftr_window_small; eauto.
  Qed.

  Section SignedWindowsWithTable.

    Variable numWindows : nat.
    Hypothesis numWindows_nz : numWindows <> 0%nat.

    Definition groupMul_signedRegular_table p n := 
      groupMul_signedRegular p (groupMul_signed_table (preCompTable p)) numWindows n.

    Theorem groupMul_signedRegular_table_correct : forall p n,
      Z.of_nat n < Z.shiftl 1 (Z.of_nat (numWindows * wsize)) ->
      groupMul_signedRegular_table p n == groupMul n p.

      intros.
      eapply groupMul_signedRegular_correct; intros.
      eapply signedMul_table_correct; trivial.
      apply preCompTable_correct.
      trivial.
      trivial.

    Qed.

    Theorem groupMul_assoc : forall a b x,
      groupMul (a * b) x == groupMul a (groupMul b x).

      induction a; intros; simpl in *.
      reflexivity.

      rewrite groupMul_distr.
      apply groupAdd_proper.
      reflexivity.
      eauto.

    Qed.


  End SignedWindowsWithTable.

End GroupMulWNAF.



