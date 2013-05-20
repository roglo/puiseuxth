(* $Id: Puiseux.v,v 1.510 2013-05-20 16:20:09 deraugla Exp $ *)

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

Lemma fst_is_nat : ∀ pol pts pt,
  points_of_ps_polynom α fld pol = pts
  → pt ∈ pts
    → ∃ n, fst pt = Qnat n.
Proof.
intros pol pts pt Hpts Hαh.
unfold points_of_ps_polynom in Hpts.
remember (al pol) as cl; clear Heqcl.
remember (an pol) as cn; clear Heqcn.
remember 0%nat as n in Hpts; clear Heqn.
unfold points_of_ps_polynom_gen in Hpts.
revert n pts Hpts Hαh.
induction cl as [| c]; intros.
 simpl in Hpts.
 destruct (is_zero_dec fld cn) as [Hz| Hnz].
  subst pts; contradiction.

  subst pts.
  destruct Hαh as [Hαh| ]; [ subst pt; simpl | contradiction ].
  exists n; reflexivity.

 simpl in Hpts.
 destruct (is_zero_dec fld c) as [Hz| Hnz].
  eapply IHcl; eassumption.

  subst pts.
  destruct Hαh as [Hαh| Hαh]; [ subst pt; simpl | idtac ].
   exists n; reflexivity.

   eapply IHcl in Hαh; [ assumption | reflexivity ].
Qed.

Lemma yyy : ∀ n pol pts hs hsl,
  pts = points_of_ps_polynom α fld pol
  → next_ch_points n pts = hsl
    → hs ∈ hsl
      → pt hs ∈ pts.
Proof.
intros n pol pts hs hsl Hpts Hnp Hhs.
bbb.
revert n pts hs Hpts Hnp Hhs.
induction hsl as [| hs₁]; [ contradiction | intros ].
destruct Hhs as [Hhs| Hhs].
 subst hs₁.
 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
 destruct pts as [| pt₂].
  injection Hnp; intros; subst hs hsl.
  simpl.
  left; reflexivity.

  injection Hnp; clear Hnp; intros Hnp Hs.
  subst hs.
  remember [pt₁; pt₂ … pts] as x; simpl; subst x.
  left; reflexivity.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
 destruct pts as [| pt₂].
  injection Hnp; clear Hnp; intros Hnp Hs.
  subst hsl; contradiction.

  injection Hnp; clear Hnp; intros Hnp Hs.
  subst hs₁.
  clear IHhsl.
  remember (minimise_slope pt₁ pt₂ pts) as ms₁.
  symmetry in Heqms₁.
  revert n pt₁ pt₂ pts hs ms₁ Hpts Hhs Hnp Heqms₁.
  induction hsl as [| hs₁]; [ contradiction | intros ].
  destruct Hhs as [Hhs| Hhs].
   subst hs₁.
   destruct n; [ discriminate Hnp | simpl in Hnp ].
   remember (rem_pts ms₁) as pts₁.
   destruct pts₁ as [| pt₃].
    injection Hnp; clear Hnp; intros Hnp; intros; subst hs.
    remember [pt₁; pt₂ … pts] as x; simpl; subst x.
    right.
    eapply end_pt_in; eassumption.

    injection Hnp; clear Hnp; intros Hnp; intros.
    subst hs.
    remember [pt₁; pt₂ … pts] as x; simpl; subst x.
    right.
    eapply end_pt_in; eassumption.

   destruct n; [ discriminate Hnp | simpl in Hnp ].
   remember (rem_pts ms₁) as pts₁.
   destruct pts₁ as [| pt₃].
    injection Hnp; clear Hnp; intros Hnp; intros; subst hsl.
    contradiction.

    injection Hnp; clear Hnp; intros Hnp; intros.
    remember (minimise_slope (end_pt ms₁) pt₃ pts₁) as ms₂.
    symmetry in Heqms₂.
    subst hs₁.
    eapply IHhsl.
     4: eassumption.
bbb.

Lemma zzz : ∀ pol pts ns,
  pts = points_of_ps_polynom α fld pol
  → ns ∈ list_map_pairs newton_segment_of_pair (lower_convex_hull_points pts)
    → fin_pt ns ∈ pts.
Proof.
intros pol pts ns Hpts Hns.
remember (lower_convex_hull_points pts) as hsl.
unfold lower_convex_hull_points in Heqhsl.
remember (length pts) as n; clear Heqn.
rename Heqhsl into Hnp; symmetry in Hnp.
remember (list_map_pairs newton_segment_of_pair hsl) as nsl.
bbb.

intros pol pts ns Hpts Hns.
remember (lower_convex_hull_points pts) as hsl.
unfold lower_convex_hull_points in Heqhsl.
remember (length pts) as n; clear Heqn.
rename Heqhsl into Hnp; symmetry in Hnp.
destruct hsl as [| hs₁]; [ contradiction | simpl in Hns ].
destruct hsl as [| hs₂]; [ contradiction | idtac ].
remember [hs₂ … hsl] as x.
destruct Hns as [Hns| Hns]; subst x.
 subst ns; simpl.
 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
 destruct pts as [| pt₂]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp H; subst hs₁.
 remember (minimise_slope pt₁ pt₂ pts) as ms₁.
 rename Heqms₁ into Hms₁; symmetry in Hms₁.
 destruct n; [ discriminate Hnp | simpl in Hnp ].
 remember (rem_pts ms₁) as pts₁.
 destruct pts₁ as [| pt₃].
  injection Hnp; clear Hnp; intros; subst hsl hs₂.
  remember [pt₁; pt₂ … pts] as x; simpl; subst x.
  right; eapply end_pt_in; eassumption.

  injection Hnp; clear Hnp; intros; subst hsl hs₂.
  remember [pt₁; pt₂ … pts] as x; simpl; subst x.
  right; eapply end_pt_in; eassumption.

bbb.
 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
 destruct pts as [| pt₂]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp H; subst hs₁.
 remember (minimise_slope pt₁ pt₂ pts) as ms₁.
 rename Heqms₁ into Hms₁; symmetry in Hms₁.
 clear Hpts.
 revert n hs₂ ms₁ pt₁ pt₂ pts ns Hns Hnp Hms₁.
 induction hsl as [| hs₃]; [ contradiction | intros ].
 destruct n; [ discriminate Hnp | simpl in Hnp ].
 remember (rem_pts ms₁) as pts₁.
 destruct pts₁ as [| pt₃]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp Hs₂.
 remember (minimise_slope (end_pt ms₁) pt₃ pts₁) as ms₂.
 rename Heqms₂ into Hms₂; symmetry in Hms₂.
 destruct Hns as [Hns| Hns].
  subst ns.
  remember [pt₁; pt₂ … pts] as x; simpl; subst x.
  destruct n; [ discriminate Hnp | simpl in Hnp ].
  remember (rem_pts ms₂) as pts₂.
  destruct pts₂ as [| pt₄].
   injection Hnp; clear Hnp; intros; subst hs₃ hsl.
   remember [pt₁; pt₂ … pts] as x; simpl; subst x.
   subst hs₂.
bbb.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
 destruct pts as [| pt₂]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp H; subst hs₁.
bbb.
*)

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
eapply fst_is_nat with (pt := ini_pt ns) in Hj₁.
 remember Heqpts as Hk₁; clear HeqHk₁; symmetry in Hk₁.
 eapply fst_is_nat with (pt := fin_pt ns) in Hk₁.
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
   destruct Hj₁ as (jn, Hjn).
   destruct Hk₁ as (kn, Hkn).
   rewrite Hjn in Hj, Hlt.
   rewrite Hkn in Hk, Hlt.
   unfold nofq, Qnat in Hj, Hk.
   simpl in Hj, Hk.
   rewrite Nat2Z.id in Hj, Hk.
   subst jn kn.
   unfold Qnat in Hlt; simpl in Hlt.
   do 2 rewrite Zmult_1_r in Hlt.
   apply Nat2Z.inj_lt; assumption.

   destruct n; [ discriminate Hnp | simpl in Hnp ].
   destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
   destruct pts as [| pt₂].
    injection Hnp; clear Hnp; intros; subst hs₁ hsl.
    discriminate Heqnsl.

    injection Hnp; clear Hnp; intros Hnp H; subst hs₁.
    simpl in Heqnsl.
    destruct hsl as [| hs₁]; [ discriminate Heqnsl | idtac ].
    remember [hs₁ … hsl] as x.
    injection Heqnsl; clear Heqnsl; intros Hnsl Hns₁; subst x.
    remember (minimise_slope pt₁ pt₂ pts) as ms.
    symmetry in Heqms.
    eapply IHhsl with (pts := [end_pt ms … rem_pts ms]); try eassumption.
    eapply minimise_slope_sorted; eassumption.

  eapply zzz; eassumption.
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
