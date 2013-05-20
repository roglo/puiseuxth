(* $Id: Puiseux.v,v 1.498 2013-05-20 05:23:14 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import Sorted.
Require Import ConvexHull.
Require Import ConvexHullMisc.
Require Import Puiseux_base.
Require Import Misc.

Definition degree α (pol : polynomial α) := List.length (al pol).
Arguments degree : default implicits.

(* Horner's algorithm *)
Definition apply_polynomial {α} fld pol (x : α) :=
  List.fold_right (λ accu coeff, add fld (mul fld accu x) coeff) (an pol)
    (al pol).
Arguments apply_polynomial : default implicits. 

Record algebraically_closed_field α :=
  { ac_field : field α;
    ac_prop : ∀ pol, degree pol ≥ 1
      → ∃ r, apply_polynomial ac_field pol r = zero ac_field }.
Arguments ac_field : default implicits.
Arguments ac_prop : default implicits.

Definition nofq q := Z.to_nat (Qnum q).

Fixpoint make_char_pol α (fld : field α) cdeg dcl n :=
  match n with
  | O => []
  | S n₁ =>
      match dcl with
      | [] =>
          [zero fld … make_char_pol α fld (S cdeg) [] n₁]
      | [(deg, coeff) … dcl₁] =>
          if eq_nat_dec deg cdeg then
            [coeff … make_char_pol α fld (S cdeg) dcl₁ n₁]
          else
            [zero fld … make_char_pol α fld (S cdeg) dcl n₁]
      end
    end.

Definition deg_coeff_of_point α pol (pt : (Q * Q)) :=
  let h := nofq (fst pt) in
  let ps := List.nth h (al pol) (an pol) in
  let c := valuation_coeff α ps in
  (h, c).

Definition characteristic_polynomial α fld pol ns :=
  let dcl := List.map (deg_coeff_of_point α pol) [ini_pt ns … oth_pts ns] in
  let j := nofq (fst (ini_pt ns)) in
  let k := nofq (fst (fin_pt ns)) in
  let cl := make_char_pol α fld j dcl (k - j) in
  let kps := List.nth k (al pol) (an pol) in
  {| al := cl; an := valuation_coeff α kps |}.

(* *)

Section field.

Variable α : Type.
Variable fld : field (puiseux_series α).

Lemma all_fst_is_int : ∀ n cl cn pts h αh,
  filter_non_zero_ps α fld (all_points_of_ps_polynom α n cl cn) = pts
  → (h, αh) ∈ pts
    → (Qden h = 1)%positive.
Proof.
intros n cl cn pts h αh Hpts Hαh.
revert n pts Hpts Hαh.
induction cl as [| c]; intros.
 simpl in Hpts.
 destruct (is_zero_dec fld cn) as [Hz| Hnz].
  subst pts; contradiction.

  subst pts.
  destruct Hαh as [Hαh| ]; [ idtac | contradiction ].
  injection Hαh; clear Hαh; intros; subst h αh.
  reflexivity.

 simpl in Hpts.
 destruct (is_zero_dec fld c) as [Hz| Hnz].
  eapply IHcl; eassumption.

  subst pts.
  destruct Hαh as [Hαh| Hαh].
   injection Hαh; clear Hαh; intros; subst h αh.
   reflexivity.

   eapply IHcl in Hαh; [ assumption | reflexivity ].
Qed.

Lemma fst_is_int : ∀ pol pts pt,
  points_of_ps_polynom α fld pol = pts
  → pt ∈ pts
    → (Qden (fst pt) = 1)%positive.
Proof.
intros pol pts (h, αh) Hpts Hαh.
eapply all_fst_is_int; eassumption.
Qed.

Lemma same_den_qeq_eq : ∀ h i, Qden h = Qden i → h == i → h = i.
Proof.
intros h i Hd Hh.
unfold Qeq in Hh.
rewrite Hd in Hh.
apply Z.mul_reg_r in Hh.
 destruct h, i.
 simpl in Hd, Hh.
 subst Qden Qnum; reflexivity.

 intros H.
 pose proof (Pos2Z.is_pos (Qden i)) as HH.
 rewrite <- H in HH.
 apply Zlt_irrefl in HH; contradiction.
Qed.

Lemma sorted_hd_not_in_tl : ∀ k αj αk pts,
  Sorted fst_lt [(k, αj) … pts] → (k, αk) ∉ pts.
Proof.
intros k αj αk pts H.
induction pts as [| (h, αh)]; [ intros HH; contradiction | idtac ].
intros HH.
destruct HH as [HH| HH].
 injection HH; clear HH; intros; subst h αh.
 apply Sorted_inv_2 in H; destruct H as (Hlt, H).
 apply Qlt_irrefl in Hlt; assumption.

 revert HH; apply IHpts.
 apply Sorted_inv_2 in H; destruct H as (Hlt₁, H).
 destruct pts as [| pt₂]; [ constructor; constructor | idtac ].
 apply Sorted_inv_2 in H; destruct H as (Hlt₂, H).
 constructor; [ assumption | idtac ].
 constructor; eapply Qlt_trans; eassumption.
Qed.

Lemma eq_k_eq_αk : ∀ pts j αj k αk,
  Sorted fst_lt pts
  → (j, αj) ∈ pts
    → (k, αk) ∈ pts
      → j = k
        → αj = αk.
Proof.
intros pts j αj k αk Hpts Hαj Hαk Hjk.
subst j.
induction pts as [| pt]; intros; [ contradiction | idtac ].
destruct Hαj as [Hαj| Hαj]; [ subst pt | idtac ].
 destruct Hαk as [Hαk| Hαk].
  injection Hαk; clear; intros; subst αj; reflexivity.

  exfalso; revert Hαk; eapply sorted_hd_not_in_tl; eassumption.

 destruct Hαk as [Hαk| Hαk]; [ subst pt | idtac ].
  exfalso; revert Hαj; eapply sorted_hd_not_in_tl; eassumption.

  destruct pts as [| pt₂]; [ contradiction | idtac ].
  apply Sorted_inv_2 in Hpts; destruct Hpts as (Hlt₁, Hpts).
  eapply IHpts; eassumption.
Qed.

Lemma same_k_same_αk : ∀ pol pts j αj k αk,
  points_of_ps_polynom α fld pol = pts
  → (j, αj) ∈ pts
    → (k, αk) ∈ pts
      → j == k
        → αj = αk.
Proof.
intros pos pts j αj k αk Hpts Hj Hk Hjk.
remember Hpts as Hsort; clear HeqHsort.
symmetry in Hsort.
unfold points_of_ps_polynom in Hsort.
apply points_of_polyn_sorted in Hsort.
eapply eq_k_eq_αk; try eassumption.
eapply all_fst_is_int in Hj; try eassumption.
eapply all_fst_is_int in Hk; try eassumption.
rewrite <- Hk in Hj.
apply same_den_qeq_eq; assumption.
Qed.

Lemma j_lt_k : ∀ pol j k ns,
  ns ∈ newton_segments fld pol
  → j = nofq (fst (ini_pt ns))
    → k = nofq (fst (fin_pt ns))
      → (j < k)%nat.
Proof.
intros pol j k ns Hns Hj Hk.
unfold newton_segments in Hns.
remember (points_of_ps_polynom α fld pol) as pts.
remember Heqpts as Hj₁; clear HeqHj₁; symmetry in Hj₁.
eapply fst_is_int with (pt := ini_pt ns) in Hj₁.
 remember Heqpts as Hk₁; clear HeqHk₁; symmetry in Hk₁.
 eapply fst_is_int with (pt := fin_pt ns) in Hk₁.
  apply points_of_polyn_sorted in Heqpts.
  rename Heqpts into Hsort.
  remember (lower_convex_hull_points pts) as hsl.
  unfold lower_convex_hull_points in Heqhsl.
  rename Heqhsl into Hnp.
  symmetry in Hnp.
  remember (length pts) as n; clear Heqn.
  remember (list_map_pairs newton_segment_of_pair hsl) as nsl.
  symmetry in Heqnsl.
  revert n pts ns nsl j k Hsort Hnp Hns Hj Hk Hj₁ Hk₁ Heqnsl.
  induction hsl as [| hs₁]; intros; [ subst nsl; contradiction | idtac ].
  destruct nsl as [| ns₁]; [ contradiction | idtac ].
  destruct Hns as [Hns| Hns].
   subst ns₁.
   simpl in Heqnsl.
   destruct hsl as [| hs₂]; [ discriminate Heqnsl | idtac ].
   injection Heqnsl; clear Heqnsl; intros Hnsl Hns.
   unfold newton_segment_of_pair in Hns.
   subst ns.
   simpl in Hj, Hk, Hj₁, Hk₁.
   apply next_points_sorted in Hnp; [ idtac | assumption ].
   apply Sorted_inv_2 in Hnp; destruct Hnp as (Hlt, Hnp).
   unfold hs_x_lt in Hlt; simpl in Hlt.
   unfold Qlt in Hlt.
   rewrite Hj₁, Hk₁ in Hlt.
   do 2 rewrite Zmult_1_r in Hlt.
   unfold nofq in Hj, Hk.
   subst j k.
bbb.
*)

Lemma cpol_degree : ∀ α fld acf pol cpol ns,
  ns ∈ newton_segments fld pol
  → cpol = characteristic_polynomial α (ac_field acf) pol ns
    → degree cpol ≥ 1.
Proof.
intros α fld acf pol cpol ns Hns Hpol.
subst cpol.
unfold characteristic_polynomial, degree; simpl.
remember (nofq (fst (ini_pt ns))) as j.
remember (nofq (fst (fin_pt ns))) as k.
remember (k - j)%nat as kj.
destruct kj; simpl.
 eapply j_lt_k with (j := j) in Hns; try eassumption.
 apply NPeano.Nat.sub_gt in Hns.
 symmetry in Heqkj; contradiction.

 rewrite <- Heqj.
 destruct (eq_nat_dec j j) as [| H]; [ apply le_n_S, le_0_n | idtac ].
 exfalso; apply H; reflexivity.
Qed.

Lemma exists_root : ∀ α fld acf pol cpol ns,
  ns ∈ newton_segments fld pol
  → cpol = characteristic_polynomial α (ac_field acf) pol ns
    → ∃ c, apply_polynomial (ac_field acf) cpol c = zero (ac_field acf).
Proof.
intros α fld acf pol cpol ns Hdeg Hpol.
eapply cpol_degree in Hdeg; [ idtac | eassumption ].
apply (ac_prop acf cpol Hdeg).
Qed.
