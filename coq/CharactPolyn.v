(* CharactPolyn.v *)

Require Import Utf8.
Require Import QArith.
Require Import Sorted.
Require Import NPeano.

Require Import ConvexHull.
Require Import ConvexHullMisc.
Require Import Misc.
Require Import Newton.
Require Import PolyConvexHull.
Require Import Polynomial.
Require Import Nbar.
Require Import Field.
Require Import Puiseux_base.
Require Import Puiseux_series.
Require Import Slope_base.

Set Implicit Arguments.

Fixpoint degree_plus_1_of_list α (is_zero : α → bool) (l : list α) :=
  match l with
  | [] => O
  | [x … l₁] =>
      match degree_plus_1_of_list is_zero l₁ with
      | O => if is_zero x then O else 1%nat
      | S n => S (S n)
      end
  end.

Definition degree α is_zero (pol : polynomial α) :=
  pred (degree_plus_1_of_list is_zero (bl pol)).

Record term α β := { coeff : α; power : β }.

(* *)

Definition apply_polynomial α (f : field α) :=
  apply_poly (fld_zero f) (fld_add f) (fld_mul f).

Record algeb_closed_field α :=
  { ac_field : field α;
    ac_root : polynomial α → (α * nat);
    ac_is_zero : α → bool;
    ac_prop : ∀ pol, degree ac_is_zero pol ≥ 1
      → apply_polynomial ac_field pol (fst (ac_root pol)) = .0 ac_field%F }.

Definition nofq q := Z.to_nat (Qnum q).

Fixpoint list_pad α n (zero : α) rem :=
  match n with
  | O => rem
  | S n₁ => [zero … list_pad n₁ zero rem]
  end.

Fixpoint make_char_pol α (f : field α) pow tl :=
  match tl with
  | [] => []
  | [t₁ … tl₁] =>
      list_pad (power t₁ - pow) .0 f%F
        [coeff t₁ … make_char_pol f (S (power t₁)) tl₁]
    end.

Definition term_of_point α (f : field α) pol (pt : (Q * Q)) :=
  let h := nofq (fst pt) in
  let ps := List.nth h (bl pol) .0 f%ps in
  let c := valuation_coeff f ps in
  {| coeff := c; power := h |}.

Definition characteristic_polynomial α (f : field α) pol ns :=
  let pl := [ini_pt ns … oth_pts ns ++ [fin_pt ns]] in
  let tl := List.map (term_of_point f pol) pl in
  let j := nofq (fst (ini_pt ns)) in
  {| bl := make_char_pol f j tl |}.

Definition series_list_com_den α (psl : list (puiseux_series α)) :=
  List.fold_right (λ ps a, Pos.mul a (ps_polord ps)) 1%positive psl.

(* *)

Section theorems.

Variable α : Type.
Variable f : field α.

Lemma pt_absc_is_nat : ∀ pol pts pt,
  points_of_ps_polynom f pol = pts
  → pt ∈ pts
    → fst pt = Qnat (Z.to_nat (Qnum (fst pt))).
Proof.
intros pol pts pt Hpts Hαh.
unfold points_of_ps_polynom in Hpts.
remember (bl pol) as cl; clear Heqcl.
remember 0%nat as n in Hpts; clear Heqn.
unfold points_of_ps_polynom_gen in Hpts.
unfold qpower_list in Hpts.
revert n pts Hpts Hαh.
induction cl as [| c]; intros; [ subst pts; contradiction | idtac ].
simpl in Hpts.
destruct cl as [| c₁].
 simpl in Hpts.
 destruct (valuation f c); subst pts; [ idtac | contradiction ].
 simpl in Hαh.
 destruct Hαh as [Hαh| ]; [ idtac | contradiction ].
 subst pt; simpl.
 rewrite Nat2Z.id; reflexivity.

 simpl in Hpts.
 simpl in IHcl.
 destruct (valuation f c).
  subst pts.
  destruct Hαh as [Hαh| Hαh].
   subst pt; simpl.
   rewrite Nat2Z.id; reflexivity.

   eapply IHcl; [ reflexivity | eassumption ].

  eapply IHcl; eassumption.
Qed.

Lemma in_seg_in_pts : ∀ pt pt₁ pt₂ pts,
  pt ∈ seg (minimise_slope pt₁ pt₂ pts)
  → pt ∈ [pt₂ … pts].
Proof.
intros pt pt₁ pt₂ pts Hpt.
revert pt₂ Hpt.
induction pts as [| pt₃]; intros; [ contradiction | idtac ].
simpl in Hpt.
remember (minimise_slope pt₁ pt₃ pts) as ms₃.
remember (slope_expr pt₁ pt₂ ?= slope ms₃) as c.
destruct c; simpl in Hpt.
 destruct Hpt as [Hpt| Hpt].
  subst pt; left; reflexivity.

  right; subst ms₃; apply IHpts; assumption.

 contradiction.

 right; subst ms₃; apply IHpts; assumption.
Qed.

Lemma hull_seg_edge_in_init_pts : ∀ n pts hs hsl pt,
  next_ch_points n pts = hsl
  → hs ∈ hsl
    → pt ∈ edge hs
      → pt ∈ pts.
Proof.
intros n pts hs hsl pt Hnp Hhs Hpt.
revert n pts hs pt Hnp Hhs Hpt.
induction hsl as [| hs₁]; [ contradiction | intros ].
destruct Hhs as [Hhs| Hhs].
 subst hs₁.
 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
 destruct pts as [| pt₂].
  injection Hnp; intros; subst hs; contradiction.

  injection Hnp; clear Hnp; intros Hnp Hhs.
  subst hs; simpl in Hpt.
  right; eapply in_seg_in_pts; eassumption.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
 destruct pts as [| pt₂].
  injection Hnp; intros; subst hsl; contradiction.

  injection Hnp; clear Hnp; intros Hnp Hs₁; subst hs₁.
  eapply IHhsl in Hhs; [ idtac | eassumption | eassumption ].
  remember (minimise_slope pt₁ pt₂ pts) as ms₁.
  symmetry in Heqms₁.
  destruct Hhs as [Hhs| Hhs].
   rewrite <- Hhs.
   right; eapply end_pt_in; eassumption.

   right; right; eapply rem_pts_in; eassumption.
Qed.

Lemma hull_seg_vert_in_init_pts : ∀ n pts hs hsl,
  next_ch_points n pts = hsl
  → hs ∈ hsl
    → vert hs ∈ pts.
Proof.
intros n pts hs hsl Hnp Hhs.
revert n pts hs Hnp Hhs.
induction hsl as [| hs₁]; [ contradiction | intros ].
destruct Hhs as [Hhs| Hhs].
 subst hs₁.
 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
 destruct pts as [| pt₂].
  injection Hnp; intros; subst hs; left; reflexivity.

  injection Hnp; clear Hnp; intros Hnp Hhs.
  subst hs; left; reflexivity.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
 destruct pts as [| pt₂].
  injection Hnp; intros; subst hsl; contradiction.

  injection Hnp; clear Hnp; intros Hnp Hs₁; subst hs₁.
  eapply IHhsl in Hhs; [ idtac | eassumption ].
  remember (minimise_slope pt₁ pt₂ pts) as ms₁.
  symmetry in Heqms₁.
  destruct Hhs as [Hhs| Hhs].
   rewrite <- Hhs.
   right; eapply end_pt_in; eassumption.

   right; right; eapply rem_pts_in; eassumption.
Qed.

Lemma oth_pts_in_init_pts : ∀ pts ns pt,
  ns ∈ list_map_pairs newton_segment_of_pair (lower_convex_hull_points pts)
  → pt ∈ oth_pts ns
    → pt ∈ pts.
Proof.
intros pts ns pt Hns Hpt.
remember (lower_convex_hull_points pts) as hsl.
unfold lower_convex_hull_points in Heqhsl.
remember (length pts) as n; clear Heqn.
rename Heqhsl into Hnp; symmetry in Hnp.
revert pts ns n Hnp Hns Hpt.
induction hsl as [| hs₁]; [ contradiction | intros ].
destruct hsl as [| hs₂]; [ contradiction | idtac ].
destruct Hns as [Hns| Hns].
 subst ns; simpl in Hpt |- *.
 eapply hull_seg_edge_in_init_pts; try eassumption.
 left; reflexivity.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
 destruct pts as [| pt₂]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hhsl Hhs₁; subst hs₁.
 eapply IHhsl in Hhsl; [ idtac | eassumption | eassumption ].
 remember (minimise_slope pt₁ pt₂ pts) as ms₂.
 symmetry in Heqms₂.
 destruct Hhsl as [Hhsl| Hhsl].
  subst pt.
  right; eapply end_pt_in; eassumption.

  right; right; eapply rem_pts_in; eassumption.
Qed.

Lemma ini_fin_ns_in_init_pts : ∀ pts ns,
  ns ∈ list_map_pairs newton_segment_of_pair (lower_convex_hull_points pts)
  → ini_pt ns ∈ pts ∧ fin_pt ns ∈ pts.
Proof.
intros pts ns Hns.
remember (lower_convex_hull_points pts) as hsl.
unfold lower_convex_hull_points in Heqhsl.
remember (length pts) as n; clear Heqn.
rename Heqhsl into Hnp; symmetry in Hnp.
revert pts ns n Hnp Hns.
induction hsl as [| hs₁]; [ contradiction | intros ].
destruct hsl as [| hs₂]; [ contradiction | idtac ].
destruct Hns as [Hns| Hns].
 subst ns; simpl.
 split.
  eapply hull_seg_vert_in_init_pts; [ eassumption | idtac ].
  left; reflexivity.

  eapply hull_seg_vert_in_init_pts; [ eassumption | idtac ].
  right; left; reflexivity.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
 destruct pts as [| pt₂]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp; intros; subst hs₁.
 eapply IHhsl in Hnp; [ idtac | eassumption ].
 remember (minimise_slope pt₁ pt₂ pts) as ms₁.
 symmetry in Heqms₁.
 destruct Hnp as (Hini, Hfin).
 split.
  destruct Hini as [Hini| Hini].
   rewrite <- Hini.
   right; eapply end_pt_in; eassumption.

   right; right; eapply rem_pts_in; eassumption.

  destruct Hfin as [Hfin| Hfin].
   rewrite <- Hfin.
   right; eapply end_pt_in; eassumption.

   right; right; eapply rem_pts_in; eassumption.
Qed.

Lemma pt₁_bef_seg : ∀ pt₁ pt₂ pts pth,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → pth ∈ seg (minimise_slope pt₁ pt₂ pts)
    → fst pt₁ < fst pth.
Proof.
intros pt₁ pt₂ pts pth Hsort Hh.
revert pt₁ pt₂ pth Hsort Hh.
induction pts as [| pt₃]; intros; [ contradiction | idtac ].
simpl in Hh.
remember (minimise_slope pt₁ pt₃ pts) as ms₃.
remember (slope_expr pt₁ pt₂ ?= slope ms₃) as c.
symmetry in Heqc.
destruct c.
 simpl in Hh.
 destruct Hh as [Hh| Hh].
  subst pth.
  eapply Sorted_hd; [ eassumption | left; reflexivity ].

  subst ms₃.
  eapply IHpts; [ idtac | eassumption ].
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

 contradiction.

 subst ms₃.
 eapply IHpts; [ idtac | eassumption ].
 eapply Sorted_minus_2nd; [ idtac | eassumption ].
 intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Lemma vert_bef_edge : ∀ pts n hs hsl j αj h αh,
  Sorted fst_lt pts
  → next_ch_points n pts = [hs … hsl]
    → (j, αj) = vert hs
      → (h, αh) ∈ edge hs
        → j < h.
Proof.
intros pts n hs hsl j αj h αh Hsort Hnp Hj Hh.
destruct pts as [| pt₁]; [ destruct n; discriminate Hnp | idtac ].
destruct n; [ discriminate Hnp | simpl in Hnp ].
destruct pts as [| pt₂].
 injection Hnp; clear Hnp; intros; subst hs hsl; contradiction.

 injection Hnp; clear Hnp; intros Hhsl Hhs.
 subst hs.
 simpl in Hj, Hh.
 apply pt₁_bef_seg in Hh; [ subst pt₁; assumption | assumption ].
Qed.

Lemma jq_lt_hq : ∀ (pol : puis_ser_pol α) j αj h αh ns,
  ns ∈ newton_segments f pol
  → (j, αj) = ini_pt ns
    → (h, αh) ∈ oth_pts ns
      → j < h.
Proof.
intros pol j αj h αh ns Hns Hjαj Hhαh.
unfold newton_segments in Hns.
remember (points_of_ps_polynom f pol) as pts.
apply points_of_polyn_sorted in Heqpts.
remember (lower_convex_hull_points pts) as hsl.
unfold lower_convex_hull_points in Heqhsl.
rename Heqhsl into Hnp.
symmetry in Hnp.
remember (length pts) as n; clear Heqn.
revert pol j αj h αh ns pts n Heqpts Hnp Hns Hjαj Hhαh.
induction hsl as [| hs₁]; intros; [ contradiction | idtac ].
destruct hsl as [| hs₂]; [ contradiction | idtac ].
rewrite list_map_pairs_cons_cons in Hns.
destruct Hns as [Hns| Hns].
 subst ns.
 simpl in Hjαj, Hhαh.
 eapply vert_bef_edge; eassumption.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ destruct n; discriminate Hnp | idtac ].
 destruct pts as [| pt₂]; [ destruct n; discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hhsl Hhs₁; subst hs₁.
 eapply IHhsl in Hhsl; try eassumption.
 eapply minimise_slope_sorted; [ eassumption | reflexivity ].
Qed.

Lemma j_lt_h : ∀ (pol : puis_ser_pol α) j αj jq h αh hq ns,
  ns ∈ newton_segments f pol
  → (jq, αj) = ini_pt ns
    → (hq, αh) ∈ oth_pts ns
      → jq = Qnat j
        → hq = Qnat h
          → (j < h)%nat.
Proof.
intros pol j αj jq h αh hq ns Hns Hj Hh Hjq Hhq.
eapply jq_lt_hq in Hh; try eassumption.
rewrite Hjq, Hhq in Hh.
unfold Qnat in Hh; simpl in Hh.
unfold Qlt in Hh; simpl in Hh.
do 2 rewrite Zmult_1_r in Hh.
apply Nat2Z.inj_lt; assumption.
Qed.

Lemma jz_lt_hz : ∀ (pol : puis_ser_pol α) jz αj jq hz αh hq ns,
  ns ∈ newton_segments f pol
  → (jq, αj) = ini_pt ns
    → (hq, αh) ∈ oth_pts ns
      → jz = Qnum jq
        → hz = Qnum hq
          → (jz < hz)%Z.
Proof.
intros pol jz αj jq hz αh hq ns Hns Hjq Hhq Hjz Hhz.
subst jz hz.
remember Hns as H; clear HeqH.
unfold newton_segments in H.
remember (points_of_ps_polynom f pol) as pts.
symmetry in Heqpts.
remember Heqpts as Hjqn; clear HeqHjqn.
apply pt_absc_is_nat with (pt := (jq, αj)) in Hjqn.
 simpl in Hjqn.
 remember Heqpts as Hhqn; clear HeqHhqn.
 apply pt_absc_is_nat with (pt := (hq, αh)) in Hhqn.
  simpl in Hhqn.
  rewrite Hjqn, Hhqn.
  simpl.
  apply inj_lt.
  eapply j_lt_h; try eassumption.

  eapply oth_pts_in_init_pts; eassumption.

 rewrite Hjq.
 eapply ini_fin_ns_in_init_pts; eassumption.
Qed.

Lemma seg_bef_end_pt : ∀ pt₁ pt₂ pts ms₁ hq αh kq αk,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms₁
    → (hq, αh) ∈ seg ms₁
      → (kq, αk) = end_pt ms₁
        → hq < kq.
Proof.
fix IHpts 3.
intros pt₁ pt₂ pts ms₁ hq αh kq αk Hsort Hms₁ Hseg Hend.
destruct pts as [| pt₃]; [ subst ms₁; contradiction | idtac ].
simpl in Hms₁.
remember (minimise_slope pt₁ pt₃ pts) as ms₂.
symmetry in Heqms₂.
remember (slope_expr pt₁ pt₂ ?= slope ms₂) as c.
symmetry in Heqc.
destruct c.
 subst ms₁; simpl in Hseg, Hend.
 destruct Hseg as [Hseg| Hseg].
  apply Sorted_inv_1 in Hsort.
  apply Sorted_hd with (pt₂ := (kq, αk)) in Hsort.
   subst pt₂; assumption.

   rewrite Hend.
   eapply end_pt_in; eassumption.

  eapply IHpts with (pts := pts); try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

 subst ms₁; simpl in Hseg, Hend; contradiction.

 subst ms₁; simpl in Hseg, Hend.
 eapply IHpts with (pts := pts); try eassumption.
 eapply Sorted_minus_2nd; [ idtac | eassumption ].
 intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Lemma edge_bef_vert : ∀ pts n hs₁ hs₂ hsl hq αh kq αk,
  Sorted fst_lt pts
  → next_ch_points n pts = [hs₁; hs₂ … hsl]
    → (hq, αh) ∈ edge hs₁
      → (kq, αk) = vert hs₂
        → hq < kq.
Proof.
intros pts n hs₁ hs₂ hsl hq αh kq αk Hsort Hnp Hh Hk.
destruct pts as [| pt₁]; [ destruct n; discriminate Hnp | idtac ].
destruct n; [ discriminate Hnp | simpl in Hnp ].
destruct pts as [| pt₂]; [ discriminate Hnp | idtac ].
injection Hnp; clear Hnp; intros Hnp H; subst hs₁.
simpl in Hh.
remember (minimise_slope pt₁ pt₂ pts) as ms₁.
symmetry in Heqms₁.
destruct n; [ discriminate Hnp | simpl in Hnp ].
remember (end_pt ms₁) as pt₃.
symmetry in Heqpt₃.
remember (rem_pts ms₁) as pts₁.
symmetry in Heqpts₁.
destruct pts₁ as [| pt₄].
 injection Hnp; clear Hnp; intros; subst hs₂ hsl.
 simpl in Hk.
 subst pt₃.
 eapply seg_bef_end_pt; eassumption.

 injection Hnp; clear Hnp; intros; subst hs₂ hsl.
 simpl in Hk.
 subst pt₃.
 eapply seg_bef_end_pt; eassumption.
Qed.

Lemma hq_lt_kq : ∀ (pol : puis_ser_pol α) hq αh kq αk ns,
  ns ∈ newton_segments f pol
  → (hq, αh) ∈ oth_pts ns
    → (kq, αk) = fin_pt ns
      → hq < kq.
Proof.
intros pol hq αh kq αk ns Hns Hoth Hfin.
unfold newton_segments in Hns.
remember (points_of_ps_polynom f pol) as pts.
apply points_of_polyn_sorted in Heqpts.
remember (lower_convex_hull_points pts) as hsl.
unfold lower_convex_hull_points in Heqhsl.
rename Heqhsl into Hnp.
symmetry in Hnp.
remember (length pts) as n; clear Heqn.
revert pol hq αh kq αk ns pts n Heqpts Hnp Hns Hoth Hfin.
induction hsl as [| hs₁]; intros; [ contradiction | idtac ].
destruct hsl as [| hs₂]; [ contradiction | idtac ].
rewrite list_map_pairs_cons_cons in Hns.
destruct Hns as [Hns| Hns].
 subst ns.
 simpl in Hoth, Hfin.
 eapply edge_bef_vert; eassumption.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₁]; [ discriminate Hnp | simpl in Hnp ].
 destruct pts as [| pt₂]; [ discriminate Hnp | simpl in Hnp ].
 injection Hnp; clear Hnp; intros Hnp H; subst hs₁.
 eapply IHhsl in Hnp; try eassumption.
 eapply minimise_slope_sorted; [ eassumption | reflexivity ].
Qed.

Lemma h_lt_k : ∀ (pol : puis_ser_pol α) h αh hq k αk kq ns,
  ns ∈ newton_segments f pol
  → (hq, αh) ∈ oth_pts ns
    → (kq, αk) = fin_pt ns
      → hq = Qnat h
        → kq = Qnat k
          → (h < k)%nat.
Proof.
intros pol h αh hq k αk kq ns Hns Hoth Hfin Hhq Hkq.
eapply hq_lt_kq in Hoth; try eassumption.
rewrite Hhq, Hkq in Hoth.
unfold Qnat in Hoth; simpl in Hoth.
unfold Qlt in Hoth; simpl in Hoth.
do 2 rewrite Zmult_1_r in Hoth.
apply Nat2Z.inj_lt; assumption.
Qed.

Lemma j_lt_k : ∀ (pol : puis_ser_pol α) j k ns,
  ns ∈ newton_segments f pol
  → j = nofq (fst (ini_pt ns))
    → k = nofq (fst (fin_pt ns))
      → (j < k)%nat.
Proof.
intros pol j k ns Hns Hj Hk.
unfold newton_segments in Hns.
remember (points_of_ps_polynom f pol) as pts.
remember Heqpts as Hj₁; clear HeqHj₁; symmetry in Hj₁.
eapply pt_absc_is_nat with (pt := ini_pt ns) in Hj₁.
 remember Heqpts as Hk₁; clear HeqHk₁; symmetry in Hk₁.
 eapply pt_absc_is_nat with (pt := fin_pt ns) in Hk₁.
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
   rewrite Hj₁ in Hj, Hlt.
   rewrite Hk₁ in Hk, Hlt.
   unfold nofq, Qnat in Hj, Hk.
   simpl in Hj, Hk.
   rewrite Nat2Z.id in Hj, Hk.
   subst j k.
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

  apply ini_fin_ns_in_init_pts; eassumption.

 apply ini_fin_ns_in_init_pts; eassumption.
Qed.

Lemma jz_lt_kz : ∀ (pol : puis_ser_pol α) jz kz ns,
  ns ∈ newton_segments f pol
  → jz = Qnum (fst (ini_pt ns))
    → kz = Qnum (fst (fin_pt ns))
      → (jz < kz)%Z.
Proof.
intros pol jz kz ns Hns Hjz Hkz.
remember Hns as H; clear HeqH.
eapply j_lt_k in H; try reflexivity.
remember (ini_pt ns) as jaj.
destruct jaj as (j, aj).
remember (fin_pt ns) as kak.
destruct kak as (k, ak).
simpl in Hjz, Hkz, H.
subst jz kz.
unfold nofq in Hns.
apply Z2Nat.inj_lt; [ idtac | idtac | assumption ].
 unfold newton_segments in Hns.
 remember (points_of_ps_polynom f pol) as pts.
 symmetry in Heqpts.
 remember Heqpts as Hpts; clear HeqHpts.
 apply pt_absc_is_nat with (pt := (j, aj)) in Hpts.
  simpl in Hpts; rewrite Hpts.
  apply Zle_0_nat.

  rewrite Heqjaj.
  apply ini_fin_ns_in_init_pts; assumption.

 unfold newton_segments in Hns.
 remember (points_of_ps_polynom f pol) as pts.
 symmetry in Heqpts.
 remember Heqpts as Hpts; clear HeqHpts.
 apply pt_absc_is_nat with (pt := (k, ak)) in Hpts.
  simpl in Hpts; rewrite Hpts.
  apply Zle_0_nat.

  rewrite Heqkak.
  apply ini_fin_ns_in_init_pts; assumption.
Qed.

(* *)

(* [Walker, p. 100]: « In the first place, we note that since each
   āi, i=0,...,n is an element of some K(x^(1/ni))', there is an
   m such that all the āi ∈ K(x^(1/m))'. Hence we have αi = mi/m. » *)
Theorem com_den_of_ps_list : ∀ (psl : list (puiseux_series α)) m,
  m = series_list_com_den psl
  → ∀ ps αi, ps ∈ psl
    → valuation f ps = Some αi
      → ∃ mi, αi == mi # m.
Proof.
intros psl m Hm ps αi Hps Hv.
apply List.in_split in Hps.
destruct Hps as (l₁, (l₂, Hpsl)).
remember (series_list_com_den (l₁ ++ l₂)) as m₁.
exists (Qnum αi * Zpos m₁)%Z.
subst m m₁ psl.
induction l₁ as [| ps₁]; simpl.
 unfold Qeq; simpl.
 rewrite Pos2Z.inj_mul.
 rewrite Zmult_assoc.
 unfold valuation in Hv.
 remember (null_coeff_range_length f (ps_terms ps) 0) as n eqn:Hn .
 symmetry in Hn.
 destruct n as [n| ]; [ idtac | discriminate Hv ].
 injection Hv; clear Hv; intros Hαi.
 subst αi; reflexivity.

 rewrite Pos2Z.inj_mul, Z.mul_assoc.
 unfold Qeq; simpl.
 rewrite Pos2Z.inj_mul.
 rewrite Z.mul_assoc, Z.mul_comm, <- Z.mul_assoc.
 symmetry; rewrite Z.mul_comm, <- Z.mul_assoc.
 apply Z.mul_cancel_l; [ apply Pos2Z_ne_0 | idtac ].
 rewrite Z.mul_comm; symmetry; assumption.
Qed.

(* [Walker, p. 100]: « If Pj and Pk are the left and right hand ends
   of the segment L, v + γ₁ u = β₁ of the Newton polygon, then
           αj + j γ₁ = αk + k γ₁
    or
               αj - αk
          γ₁ = ------- = [...]
                k - j
  » *)
Theorem gamma_value_jk : ∀ hsl ns j k αj αk,
  ns ∈ list_map_pairs newton_segment_of_pair hsl
  → (j, αj) = ini_pt ns
    → (k, αk) = fin_pt ns
      → γ ns = (αj - αk) / (k - j).
Proof.
intros hsl ns j k αj αk Hns Hjαj Hkαk.
induction hsl as [| ((x₁, y₁), seg)]; [ contradiction | idtac ].
destruct hsl as [| ((x₂, y₂), seg₂)]; [ contradiction | idtac ].
rewrite list_map_pairs_cons_cons in Hns.
destruct Hns as [Hns| Hns].
 subst ns.
 simpl in Hjαj, Hkαk |- *.
 injection Hjαj; clear Hjαj; intros; subst x₁ y₁.
 injection Hkαk; clear Hkαk; intros; subst x₂ y₂.
 reflexivity.

 apply IHhsl; assumption.
Qed.

Lemma first_power_le : ∀ pow cl h hv,
  (h, hv) ∈ filter_finite_val f (qpower_list pow cl)
  → pow ≤ Z.to_nat (Qnum h).
Proof.
intros pow cl h hv Hhhv.
unfold qpower_list in Hhhv.
revert pow Hhhv.
induction cl as [| c]; intros; [ contradiction | idtac ].
simpl in Hhhv.
destruct cl as [| c₁].
 simpl in Hhhv.
 destruct (valuation f c); [ idtac | contradiction ].
 destruct Hhhv as [Hhhv| ]; [ idtac | contradiction ].
 injection Hhhv; clear Hhhv; intros; subst h hv.
 simpl.
 rewrite Nat2Z.id; reflexivity.

 simpl in Hhhv.
 simpl in IHcl.
 destruct (valuation f c).
  destruct Hhhv as [Hhhv| Hhhv].
   injection Hhhv; clear Hhhv; intros; subst h hv.
   simpl; rewrite Nat2Z.id; reflexivity.

   apply IHcl in Hhhv.
   transitivity (S pow); [ apply Nat.le_succ_r | assumption ].
   left; reflexivity.

  apply IHcl in Hhhv.
  transitivity (S pow); [ apply Nat.le_succ_r | assumption ].
  left; reflexivity.
Qed.

Lemma simpl_match_1 : ∀ α β (g : list α → list β) x l,
  g [] = []
  → match l with
    | [] => [x]
    | [_ … _] => [x … g l]
    end = [x … g l].
Proof.
intros.
destruct l; [ rewrite H; reflexivity | reflexivity ].
Qed.

Lemma simpl_map_qpower : ∀ α pow (c : puiseux_series α) cl,
  List.map (pair_rec (λ pow ps, (Qnat pow, ps)))
    [(pow, c) … power_list (S pow) cl] =
  qpower_list pow [c … cl].
Proof.
intros; simpl.
unfold qpower_list; simpl.
rewrite simpl_match_1; reflexivity.
Qed.

Lemma in_pts_in_ppl : ∀ pow cl ppl pts h hv hps def,
  ppl = qpower_list pow cl
  → pts = filter_finite_val f ppl
    → (h, hv) ∈ pts
      → hps = List.nth (Z.to_nat (Qnum h) - pow) cl def
        → (h, hps) ∈ ppl ∧ valuation f hps = Some hv.
Proof.
intros pow cl ppl pts h hv hps def Hppl Hpts Hhhv Hhps.
subst ppl pts.
destruct cl as [| c₁]; intros; [ contradiction | idtac ].
revert pow c₁ h hv hps Hhps Hhhv.
induction cl as [| c]; intros.
 simpl in Hhhv.
 remember (valuation f c₁) as v.
 symmetry in Heqv.
 destruct v as [v| ]; [ idtac | contradiction ].
 destruct Hhhv as [Hhhv| ]; [ idtac | contradiction ].
 injection Hhhv; clear Hhhv; intros; subst v h.
 remember (Qnum (Qnat pow)) as x; simpl in Heqx; subst x.
 rewrite Nat2Z.id, minus_diag in Hhps.
 simpl in Hhps; subst hps.
 split; [ left; reflexivity | assumption ].

 simpl in Hhhv.
 remember (valuation f c₁) as v.
 symmetry in Heqv.
 destruct v as [v| ].
  destruct Hhhv as [Hhhv| Hhhv].
   injection Hhhv; clear Hhhv; intros; subst v h.
   remember (Qnum (Qnat pow)) as x; simpl in Heqx; subst x.
   rewrite Nat2Z.id, minus_diag in Hhps.
   simpl in Hhps; subst hps.
   split; [ left; reflexivity | assumption ].

   destruct (le_dec (S pow) (Z.to_nat (Qnum h))) as [Hle| Hgt].
    eapply IHcl in Hhhv.
     rewrite <- Nat.sub_succ in Hhps.
     rewrite <- minus_Sn_m in Hhps; [ idtac | assumption ].
     simpl in Hhps.
     destruct Hhhv as (Hhhv, Hhv).
     split; [ right; eassumption | assumption ].

     rewrite <- Nat.sub_succ in Hhps.
     rewrite <- minus_Sn_m in Hhps; [ idtac | assumption ].
     simpl in Hhps; eassumption.

    rewrite simpl_match_1 in Hhhv; [ idtac | reflexivity ].
    rewrite simpl_map_qpower in Hhhv.
    apply first_power_le in Hhhv; contradiction.

  destruct (le_dec (S pow) (Z.to_nat (Qnum h))) as [Hle| Hgt].
   eapply IHcl in Hhhv.
    rewrite <- Nat.sub_succ in Hhps.
    rewrite <- minus_Sn_m in Hhps; [ idtac | assumption ].
    simpl in Hhps.
    destruct Hhhv as (Hhhv, Hhv).
    split; [ right; eassumption | assumption ].

    rewrite <- Nat.sub_succ in Hhps.
    rewrite <- minus_Sn_m in Hhps; [ idtac | assumption ].
    simpl in Hhps; eassumption.

   rewrite simpl_match_1 in Hhhv; [ idtac | reflexivity ].
   rewrite simpl_map_qpower in Hhhv.
   apply first_power_le in Hhhv; contradiction.
Qed.

Lemma in_pts_in_psl : ∀ pow pts psl h hv hps def,
  pts = filter_finite_val f (qpower_list pow psl)
  → (h, hv) ∈ pts
    → hps = List.nth (Z.to_nat (Qnum h) - pow) psl def
      → hps ∈ psl ∧ valuation f hps = Some hv.
Proof.
intros pow pts psl h hv hps def Hpts Hhv Hhps.
remember (power_list pow psl) as ppl.
assert (pow ≤ Z.to_nat (Qnum h)) as H.
 subst pts ppl.
 eapply first_power_le; eassumption.

 eapply in_pts_in_ppl in Hhv; try eassumption; [ idtac | reflexivity ].
 destruct Hhv as (Hhps₁, Hv).
 split; [ idtac | assumption ].
 subst ppl.
 destruct psl as [| ps₁]; [ contradiction | idtac ].
 revert pow pts ps₁ h hv hps Hhps Hv Hhps₁ Hpts H.
 induction psl as [| ps]; intros.
  destruct Hhps₁ as [Hhps₁| ]; [ idtac | contradiction ].
  injection Hhps₁; clear Hhps₁; intros; subst h hps.
  left; reflexivity.

  destruct Hhps₁ as [Hhps₁| Hhps₁].
   injection Hhps₁; clear Hhps₁; intros; subst h hps.
   left; reflexivity.

   destruct (eq_nat_dec (Z.to_nat (Qnum h)) pow) as [Heq| Hne].
    rewrite Heq, minus_diag in Hhps.
    subst hps; left; reflexivity.

    right.
    eapply IHpsl; try eassumption; try reflexivity.
     rewrite <- Nat.sub_succ in Hhps.
     rewrite <- minus_Sn_m in Hhps; [ assumption | idtac ].
     apply not_eq_sym in Hne.
     apply le_neq_lt; assumption.

     apply not_eq_sym in Hne.
     apply le_neq_lt; assumption.
Qed.

Lemma in_pts_in_pol : ∀ pol pts h hv hps def,
  pts = points_of_ps_polynom f pol
  → (Qnat h, hv) ∈ pts
    → hps = List.nth h (bl pol) def
      → hps ∈ bl pol ∧ valuation f hps = Some hv.
Proof.
intros pol pts h hv hps def Hpts Hhhv Hhps.
eapply in_pts_in_psl; try eassumption.
simpl; rewrite Nat.sub_0_r, Nat2Z.id; eassumption.
Qed.

Lemma p_mq_formula : ∀ m j k mj mk g,
  (0 < k - j)%Z
  → g = Z.gcd (mj - mk) (k - j)
    → ((mj # m) - (mk # m)) / ((k # 1) - (j # 1)) ==
       (mj - mk) / g # m * Z.to_pos ((k - j) / g).
Proof.
intros m j k mj mk g Hkj Hg.
do 2 rewrite <- Qnum_minus_distr_r.
destruct (Z.eq_dec (mj - mk) 0)%Z as [Hz| Hnz].
 rewrite Hz; simpl.
 reflexivity.

 rewrite Qdiv_mul; [ idtac | assumption | assumption ].
 unfold Qeq.
 simpl.
 do 2 rewrite Pos2Z.inj_mul.
 rewrite Z.mul_comm; symmetry.
 rewrite Z.mul_comm; symmetry.
 do 2 rewrite <- Z.mul_assoc.
 apply Z.mul_cancel_l; [ apply Pos2Z_ne_0 | idtac ].
 rewrite Zmult_1_r.
 pose proof (Z.gcd_divide_r (mj - mk) (k - j)) as H.
 destruct H as (u, Hu).
 rewrite <- Hg in Hu.
 rewrite Hu.
 rewrite Z_div_mult_full.
  pose proof (Z.gcd_divide_l (mj - mk) (k - j)) as H.
  destruct H as (v, Hv).
  rewrite <- Hg in Hv.
  rewrite Hv.
  rewrite Z_div_mult_full.
   rewrite Z2Pos.id.
    rewrite Z2Pos.id.
     rewrite Z.mul_shuffle0, Z.mul_assoc; reflexivity.

     rewrite <- Hu; assumption.

    remember Hkj as H; clear HeqH.
    rewrite Hu in H.
    eapply Zmult_lt_0_reg_r; [ idtac | eassumption ].
    destruct g.
     symmetry in Hg.
     rewrite Zmult_0_r in Hv.
     contradiction.

     apply Pos2Z.is_pos.

     pose proof (Z.gcd_nonneg (mj - mk) (k - j)) as Hgp.
     rewrite <- Hg in Hgp.
     apply Zle_not_lt in Hgp.
     exfalso; apply Hgp.
     apply Zlt_neg_0.

   rewrite Hg; intros H; apply Z.gcd_eq_0_l in H.
   contradiction.

  rewrite Hg; intros H; apply Z.gcd_eq_0_l in H.
  contradiction.
Qed.

Lemma exists_ini_pt_nat : ∀ pol ns,
  ns ∈ newton_segments f pol
  → ∃ i αi, ini_pt ns = (Qnat i, αi).
Proof.
intros pol ns Hns.
remember (ini_pt ns) as ii.
destruct ii as ((inum, iden), αi).
exists (Z.to_nat inum), αi.
unfold newton_segments in Hns.
remember (points_of_ps_polynom f pol) as pts.
symmetry in Heqpts.
apply ini_fin_ns_in_init_pts in Hns.
destruct Hns as (Hns, _).
eapply pt_absc_is_nat in Heqpts; [ idtac | eassumption ].
rewrite <- Heqii in Heqpts; simpl in Heqpts.
rewrite Heqpts; reflexivity.
Qed.

Lemma exists_fin_pt_nat : ∀ pol ns,
  ns ∈ newton_segments f pol
  → ∃ i αi, fin_pt ns = (Qnat i, αi).
Proof.
intros pol ns Hns.
remember (fin_pt ns) as ii.
destruct ii as ((inum, iden), αi).
exists (Z.to_nat inum), αi.
unfold newton_segments in Hns.
remember (points_of_ps_polynom f pol) as pts.
symmetry in Heqpts.
apply ini_fin_ns_in_init_pts in Hns.
destruct Hns as (_, Hns).
eapply pt_absc_is_nat in Heqpts; [ idtac | eassumption ].
rewrite <- Heqii in Heqpts; simpl in Heqpts.
rewrite Heqpts; reflexivity.
Qed.

(* [Walker, p. 100]: «
                        p
          γ₁ = [...] = ---
                       m q

     where q > 0 and p and q are integers having no common factor. » *)

Theorem gamma_eq_p_nq : ∀ pol ns m,
  ns ∈ newton_segments f pol
  → m = series_list_com_den (bl pol)
    → ∃ (p : Z) (q : positive),
      γ ns == p # (m * q) ∧ Z.gcd p (' q) = 1%Z.
Proof.
(* À nettoyer *)
intros pol ns m Hns Hm.
remember Hns as Hini; clear HeqHini.
remember Hns as Hfin; clear HeqHfin.
apply exists_ini_pt_nat in Hini.
apply exists_fin_pt_nat in Hfin.
destruct Hini as (j, (αj, Hini)).
destruct Hfin as (k, (αk, Hfin)).
remember (points_of_ps_polynom f pol) as pts.
remember (lower_convex_hull_points pts) as hsl.
remember Hns as Hg; clear HeqHg.
symmetry in Hini, Hfin.
eapply gamma_value_jk in Hg; try eassumption.
subst hsl.
remember (List.nth j (bl pol) .0 f%ps) as jps.
eapply in_pts_in_pol with (hv := αj) in Heqjps; try eassumption.
 2: rewrite Hini.
 2: apply ini_fin_ns_in_init_pts.
 2: unfold newton_segments in Hns.
 2: rewrite <- Heqpts in Hns; assumption.

 destruct Heqjps as (Hjps, Hjv).
 eapply com_den_of_ps_list in Hjv; try eassumption.
 destruct Hjv as (mj, Hαj).
 remember (List.nth k (bl pol) .0 f%ps) as kps.
 eapply in_pts_in_pol with (hv := αk) in Heqkps; try eassumption.
  2: rewrite Hfin.
  2: apply ini_fin_ns_in_init_pts.
  2: unfold newton_segments in Hns.
  2: rewrite <- Heqpts in Hns; assumption.

  destruct Heqkps as (Hkps, Hkv).
  eapply com_den_of_ps_list in Hkv; try eassumption.
  destruct Hkv as (mk, Hαk).
  rewrite Hg.
  setoid_rewrite Hαj.
  setoid_rewrite Hαk.
  remember (Z.gcd (mj - mk) (Z.of_nat k - Z.of_nat j)) as g.
  exists ((mj - mk) / g)%Z.
  exists (Z.to_pos ((Z.of_nat k - Z.of_nat j) / g)).
  split.
   apply p_mq_formula; [ idtac | assumption ].
   rewrite <- Nat2Z.inj_sub.
    rewrite <- Nat2Z.inj_0.
    apply Nat2Z.inj_lt.
    apply Nat.lt_add_lt_sub_r; simpl.
    eapply j_lt_k.
     subst pts; eassumption.

     rewrite <- Hini; simpl.
     unfold nofq, Qnat; simpl.
     rewrite Nat2Z.id; reflexivity.

     rewrite <- Hfin; simpl.
     unfold nofq, Qnat; simpl.
     rewrite Nat2Z.id; reflexivity.

    apply Nat.lt_le_incl.
    eapply j_lt_k.
     subst pts; eassumption.

     rewrite <- Hini; simpl.
     unfold nofq, Qnat; simpl.
     rewrite Nat2Z.id; reflexivity.

     rewrite <- Hfin; simpl.
     unfold nofq, Qnat; simpl.
     rewrite Nat2Z.id; reflexivity.

   assert (Qnum j < Qnum k)%Z as Hjk.
    remember Heqpts as Hjn; clear HeqHjn.
    symmetry in Hjn.
    apply pt_absc_is_nat with (pt := ini_pt ns) in Hjn.
     rewrite <- Heqjj in Hjn; simpl in Hjn.
     remember Heqpts as Hkn; clear HeqHkn.
     symmetry in Hkn.
     apply pt_absc_is_nat with (pt := fin_pt ns) in Hkn.
      rewrite <- Heqkk in Hkn; simpl in Hkn.
      rewrite Hjn, Hkn in Heqg |- *; simpl in Heqg |- *.
      apply Nat2Z.inj_lt.
      eapply j_lt_k.
       subst pts; eassumption.

       rewrite <- Heqjj, Hjn; reflexivity.

       rewrite <- Heqkk, Hkn; reflexivity.

      apply ini_fin_ns_in_init_pts; assumption.

     apply ini_fin_ns_in_init_pts; assumption.

    assert (g ≠ 0%Z) as Hgnz.
     rewrite Heqg; intros H.
     apply Z.gcd_eq_0_r in H.
     apply Zminus_eq in H.
     symmetry in H; revert H.
     apply Z.lt_neq; assumption.

     rewrite Z2Pos.id.
      apply Z.gcd_div_gcd; assumption.

      apply Z.div_str_pos.
      split.
       assert (0 <= g)%Z.
        rewrite Heqg; apply Z.gcd_nonneg.

        apply Z.gt_lt, Znot_le_gt.
        intros HH.
        apply Hgnz.
        apply Z.le_antisymm; assumption.

       pose proof (Z.gcd_divide_r (mj - mk) (Qnum k - Qnum j)) as H.
       rewrite <- Heqg in H.
       destruct H as (v, H).
       destruct v as [| v| v].
        simpl in H.
        apply Zminus_eq in H.
        rewrite H in Hjk.
        apply Z.lt_irrefl in Hjk; contradiction.

        rewrite H.
        remember (' v * g)%Z as x.
        replace g with (1 * g)%Z by apply Zmult_1_l.
        subst x.
        apply Zmult_le_compat_r.
         replace 1%Z with (Z.succ 0)%Z by reflexivity.
         apply Zlt_le_succ.
         apply Pos2Z.is_pos.

         rewrite Heqg.
         apply Z.gcd_nonneg.

        exfalso.
        assert (Z.neg v * g < 0)%Z as Hn.
         apply Z.mul_neg_pos.
          apply Zlt_neg_0.

          assert (0 <= g)%Z.
           rewrite Heqg; apply Z.gcd_nonneg.

           apply Z.gt_lt, Znot_le_gt.
           intros HH.
           apply Hgnz, Z.le_antisymm; assumption.

         rewrite <- H in Hn.
         apply Zlt_not_le in Hn.
         apply Hn.
         apply Z.lt_le_incl.
         revert Hjk; clear; intros; omega.
Qed.

(* [Walker, p. 100]: « If Ph is on L, then also
                   αj - αh
      [...] = γ₁ = ------- = [...]
                    h - j
   » *)
Theorem gamma_value_jh : ∀ pol ns j αj,
  ns ∈ newton_segments f pol
  → (j, αj) = ini_pt ns
    → ∀ h αh, (h, αh) ∈ oth_pts ns
      → γ ns == (αj - αh) / (h - j).
Proof.
intros pol ns j αj Hns Hjαj h αh Hhαh.
remember Hns as Hh; clear HeqHh.
apply points_in_any_newton_segment with (h := h) (αh := αh) in Hh.
 apply Qeq_plus_minus_eq_r in Hh.
 remember Hns as Haj; clear HeqHaj.
 apply points_in_any_newton_segment with (h := j) (αh := αj) in Haj.
  rewrite <- Hh, Haj.
  field.
  apply Qlt_not_0.
  eapply jq_lt_hq; try eassumption.

  left; rewrite Hjαj; reflexivity.

 right; right; assumption.
Qed.

Lemma eq_Qeq : ∀ a b, a = b → a == b.
Proof. intros a b H; subst a; reflexivity. Qed.

Open Scope Z_scope.

Lemma pmq_qmpm : ∀ m p q j k jz kz mj mk,
  (j < k)%nat
  → jz = Z.of_nat j
    → kz = Z.of_nat k
      → p # m * q == (mj - mk # m) / (kz - jz # 1)
        → ' q * (mj - mk) = p * (kz - jz).
Proof.
intros m p q j k jz kz mj mk Hjk Hjz Hkz Hpq.
subst jz kz.
unfold Qeq in Hpq; simpl in Hpq.
do 2 rewrite Pos2Z.inj_mul in Hpq.
rewrite Zmult_comm in Hpq; symmetry in Hpq.
rewrite Zmult_comm in Hpq; symmetry in Hpq.
do 2 rewrite <- Zmult_assoc in Hpq.
apply Z.mul_cancel_l in Hpq; [ idtac | apply Pos2Z_ne_0 ].
rewrite Zmult_assoc, Zmult_comm in Hpq.
rewrite Qden_inv in Hpq.
 rewrite Qnum_inv in Hpq.
  symmetry in Hpq.
  rewrite Zmult_comm in Hpq.
  symmetry in Hpq.
  apply Z.div_unique_exact in Hpq; [ idtac | apply Pos2Z_ne_0 ].
  rewrite Hpq.
  rewrite Znumtheory.Zdivide_Zdiv_eq_2.
   rewrite Zdiv_1_r; reflexivity.

   apply Pos2Z.is_pos.

   apply Z.divide_1_l.

  apply Z.lt_0_sub, inj_lt; assumption.

 apply Z.lt_0_sub, inj_lt; assumption.
Qed.

(* [Walker, p. 100]: « In the first place, we note that [...]

         q (mj - mh) = p (h - j)
   » *)
Theorem q_mj_mk_eq_p_h_j : ∀ pol ns j αj k αk m,
  ns ∈ newton_segments f pol
  → (Qnat j, αj) = ini_pt ns
    → (Qnat k, αk) = fin_pt ns
      → m = series_list_com_den (bl pol)
        → ∃ mj mk, αj == mj # m ∧ αk == mk # m
          ∧ ∃ p q, Z.gcd p (Z.of_nat q) = 1
            ∧ Z.of_nat q * (mj - mk) = p * Z.of_nat (k - j)
            ∧ ∀ h αh, (Qnat h, αh) ∈ oth_pts ns
              → ∃ mh, αh == mh # m
                ∧ Z.of_nat q * (mj - mh) = p * Z.of_nat (h - j).
Proof.
intros pol ns j αj k αk m Hns Hj Hk Heqm.
remember Heqm as Hm; clear HeqHm.
eapply gamma_eq_p_nq in Heqm; [ idtac | eassumption ].
destruct Heqm as (p, (q, (Hgamma, Hgcd))).
remember (points_of_ps_polynom f pol) as pts.
rename Heqpts into Hpts.
bbb.
remember (List.nth (Z.to_nat (Qnum (Qnat j))) (bl pol) .0 f%ps) as jps.
eapply in_pts_in_pol in Heqjps; try eassumption.
 2: apply ini_fin_ns_in_init_pts in Hns.
 2: destruct Hns as (Hns, _).
 2: rewrite <- Hj, <- Hpts in Hns.
 2: eassumption.

 destruct Heqjps as (Hmj, Hjv).
 eapply com_den_of_ps_list in Hmj; try eassumption.
 destruct Hmj as (mj, Hmj).
 exists mj.
 remember (List.nth (Z.to_nat (Qnum (Qnat k))) (bl pol) .0 f%ps) as kps.
 eapply in_pts_in_pol in Heqkps; try eassumption.
  2: apply ini_fin_ns_in_init_pts in Hns.
  2: destruct Hns as (_, Hns).
  2: rewrite <- Hk, <- Hpts in Hns.
  2: eassumption.

  destruct Heqkps as (Hmk, Hkv).
  eapply com_den_of_ps_list in Hmk; try eassumption.
  destruct Hmk as (mk, Hmk).
  exists mk.
  split; [ assumption | idtac ].
  split; [ assumption | idtac ].
  exists p, q.
  split; [ assumption | idtac ].
  remember (inject_Z j) as jq.
  remember (inject_Z k) as kq.
  remember Hpts as Hjn; clear HeqHjn.
  symmetry in Hjn.
  apply pt_absc_is_nat with (pt := (jq, αj)) in Hjn.
   remember Hpts as Hkn; clear HeqHkn.
   symmetry in Hkn.
   apply pt_absc_is_nat with (pt := (kq, αk)) in Hkn.
    split.
     remember Hns as Hgh; clear HeqHgh.
     eapply gamma_value_jk in Hgh; try eassumption.
     apply eq_Qeq in Hgh.
     rewrite Hmj, Hmk in Hgh.
     rewrite <- Qnum_minus_distr_r in Hgh.
     rewrite Heqjq, Heqkq in Hgh.
     rewrite Hgamma in Hgh.
     unfold inject_Z in Hgh.
     rewrite <- Qnum_minus_distr_r in Hgh.
     eapply pmq_qmpm; try eassumption.
      eapply j_lt_k; try eassumption; reflexivity.

      unfold nofq.
      rewrite <- Hj; simpl.
      rewrite Z2Nat.id; [ rewrite Heqjq; reflexivity | idtac ].
      simpl in Hjn; rewrite Hjn; simpl.
      apply Zle_0_nat.

      unfold nofq.
      rewrite <- Hk; simpl.
      rewrite Z2Nat.id; [ rewrite Heqkq; reflexivity | idtac ].
      simpl in Hkn; rewrite Hkn; simpl.
      apply Zle_0_nat.

     intros h αh Hh.
     remember (inject_Z h) as hq.
     remember Hpts as Hhn; clear HeqHhn.
     symmetry in Hhn.
     apply pt_absc_is_nat with (pt := (hq, αh)) in Hhn.
      remember (List.nth (Z.to_nat (Qnum hq)) (bl pol) .0 f%ps) as hps.
      eapply in_pts_in_pol in Heqhps; try eassumption.
       2: eapply oth_pts_in_init_pts in Hns; [ idtac | eassumption ].
       2: rewrite Hpts; eassumption.

       destruct Heqhps as (Hhps, Hhv).
       eapply com_den_of_ps_list in Hhps; try eassumption.
       destruct Hhps as (mh, Hmh).
       exists mh.
       split; [ assumption | idtac ].
       remember Hns as Hgh; clear HeqHgh.
       eapply gamma_value_jh in Hgh; try eassumption.
       rewrite Hmj, Hmh in Hgh.
       rewrite <- Qnum_minus_distr_r in Hgh.
       rewrite Hgamma in Hgh.
       unfold inject_Z in Hgh.
       eapply pmq_qmpm; try eassumption.
        eapply j_lt_h; eassumption.

        unfold Qnat in Hjn.
        rewrite Heqjq in Hjn |- *.
        unfold inject_Z in Hjn; simpl in Hjn.
        injection Hjn; intros jj; assumption.

        unfold Qnat in Hhn.
        rewrite Heqhq in Hhn |- *.
        unfold inject_Z in Hhn; simpl in Hhn.
        injection Hhn; intros hh; assumption.

        rewrite Heqhq, Heqjq in Hgh.
        unfold inject_Z in Hgh.
        rewrite <- Qnum_minus_distr_r in Hgh.
        eassumption.

      unfold newton_segments in Hns.
      rewrite <- Hpts in Hns.
      eapply oth_pts_in_init_pts; eassumption.

    unfold newton_segments in Hns.
    rewrite <- Hpts in Hns.
    rewrite Hk.
    apply ini_fin_ns_in_init_pts; assumption.

   unfold newton_segments in Hns.
   rewrite <- Hpts in Hns.
   rewrite Hj.
   apply ini_fin_ns_in_init_pts; assumption.
Qed.

(* [Walker, p. 100]: « In the first place, we note that [...]
   and since p and q have no common factors, q is a factor
  of h - j. » *)
Theorem q_is_factor_of_h_minus_j : ∀ pol ns j αj k αk m,
  ns ∈ newton_segments f pol
  → (Qnat j, αj) = ini_pt ns
    → (Qnat k, αk) = fin_pt ns
      → m = series_list_com_den (bl pol)
        → ∃ mj mk, αj == mj # m ∧ αk == mk # m
          ∧ ∃ p q, Z.gcd p (Z.of_nat q) = 1
            ∧ (q | k - j)%nat
            ∧ ∀ h αh, (Qnat h, αh) ∈ oth_pts ns
              → ∃ mh, αh == mh # m
                ∧ (q | h - j)%nat.
Proof.
intros pol ns j αj k αk m Hns Hj Hk Heqm.
eapply q_mj_mk_eq_p_h_j in Hns; try eassumption.
bbb.
destruct Hns as (mj, (mk, (Hmj, (Hmk, (p, (q, (Hgcd, (Hqjk, H)))))))).
exists mj, mk.
split; [ assumption | idtac ].
split; [ assumption | idtac ].
exists p, q.
split; [ assumption | idtac ].
split.
 rewrite Z.gcd_comm in Hgcd.
 eapply Z.gauss; [ idtac | eassumption ].
 rewrite <- Hqjk.
 apply Z.divide_factor_l.

 intros h αh Hm.
 apply H in Hm.
 destruct Hm as (mh, (Hmh, Heq)).
 exists mh.
 split; [ assumption | idtac ].
 rewrite Z.gcd_comm in Hgcd.
 eapply Z.gauss; [ idtac | eassumption ].
 rewrite <- Heq.
 apply Z.divide_factor_l.
Qed.

(* [Walker, p. 100]: « In the first place, we note that [...]
   Thus for every Ph on L we have h = j + s q, s being a
   non-negative integer. » *)
Theorem h_is_j_plus_sq : ∀ pol ns j αj k αk m,
  ns ∈ newton_segments f pol
  → (Qnat j, αj) = ini_pt ns
    → (Qnat k, αk) = fin_pt ns
      → m = series_list_com_den (bl pol)
        → ∃ mj mk, αj == mj # m ∧ αk == mk # m
          ∧ ∃ p q, Z.gcd p (Z.of_nat q) = 1
            ∧ (∃ sk, k = j + sk * q)%nat
            ∧ ∀ h αh, (Qnat h, αh) ∈ oth_pts ns
              → ∃ mh s, αh == mh # m ∧ h = (j + s * q)%nat.
Proof.
intros pol ns j αj k αk m Hns Hj Hk Heqm.
remember Hns as H; clear HeqH.
eapply q_is_factor_of_h_minus_j in H; try eassumption.
bbb.
destruct H as (mj, (mk, (Hmj, (Hmk, (p, (q, (Hgcd, (Hqjk, H)))))))).
exists mj, mk.
split; [ assumption | idtac ].
split; [ assumption | idtac ].
exists p, q.
split; [ assumption | idtac ].
split.
 destruct Hqjk as (sk, Hqjk).
 destruct sk as [| sk| sk].
  simpl in Hqjk.
  apply Zminus_eq in Hqjk.
  exfalso.
  symmetry in Hqjk.
  revert Hqjk.
  apply Z.lt_neq.
  eapply jz_lt_kz; [ eassumption | idtac | idtac ].
   rewrite <- Hj; reflexivity.

   rewrite <- Hk; reflexivity.

  exists sk.
  rewrite <- Hqjk.
  rewrite Zplus_minus; reflexivity.

  apply jz_lt_kz with (jz := j) (kz := k) in Hns.
   apply Z.sub_le_lt_mono with (n := k) (m := k) in Hns.
    rewrite Zminus_diag in Hns.
    rewrite Hqjk in Hns.
    simpl in Hns.
    apply Zlt_not_le in Hns.
    exfalso; apply Hns.
    apply Z.lt_le_incl.
    apply Zlt_neg_0.

    reflexivity.

   rewrite <- Hj; reflexivity.

   rewrite <- Hk; reflexivity.

 intros h αh Hm.
 remember Hm as HH; clear HeqHH.
 apply H in HH.
 destruct HH as (mh, (Hmh, Heq)).
 exists mh.
 destruct Heq as (sh, Hq).
 destruct sh as [| sh| sh].
  simpl in Hq.
  apply Zminus_eq in Hq.
  eapply jz_lt_hz with (hz := h) in Hm; try eassumption; try reflexivity.
  apply Zlt_irrefl in Hm; contradiction.

  exists sh.
  split; [ assumption | idtac ].
  rewrite <- Hq.
  rewrite Zplus_minus; reflexivity.

  eapply jz_lt_hz with (hz := h) in Hns; try eassumption; try reflexivity.
  simpl in Hns.
  apply Z.sub_move_r in Hq.
  rewrite Hq in Hns.
  replace j with (0 + j)%Z in Hns by reflexivity.
  rewrite Zplus_assoc, Zplus_0_r in Hns.
  apply Zplus_lt_reg_r in Hns.
  apply Zlt_not_le in Hns.
  exfalso; apply Hns.
  apply Z.lt_le_incl.
  apply Zlt_neg_0.
Qed.

(* *)

Definition is_polynomial_in_x_power_q pol q :=
  ∀ i c, (i mod q ≠ 0)%nat
  → c = List.nth i (bl pol) .0 f%F
    → (c .= f .0 f)%F.

Lemma list_nth_pad_lt : ∀ i s (v : α) cl d,
  (i < s)%nat
  → List.nth i (list_pad s v cl) d = v.
Proof.
intros i s v cl d His.
revert i His.
induction s; intros.
 exfalso; revert His; apply lt_n_0.

 simpl.
 destruct i; [ reflexivity | idtac ].
 apply IHs, lt_S_n; assumption.
Qed.

Lemma list_nth_plus_pad : ∀ i s (v : α) cl d,
  List.nth (i + s) (list_pad s v cl) d = List.nth i cl d.
Proof.
intros i s v cl d.
induction s; intros.
 rewrite plus_0_r; reflexivity.

 rewrite <- plus_n_Sm; assumption.
Qed.

Open Scope nat_scope.

Lemma nth_minus_char_pol_plus_cons : ∀ i j s t tl d,
  s ≤ i
  → j + s ≤ power t
    → List.nth (i - s) (make_char_pol f (j + s) [t … tl]) d =
      List.nth i (make_char_pol f j [t … tl]) d.
Proof.
intros i j s t tl d Hsi Hjsk.
revert i j t tl d Hsi Hjsk.
induction s; intros.
 rewrite plus_0_r, Nat.sub_0_r; reflexivity.

 symmetry.
 rewrite <- IHs.
  destruct i.
   exfalso; revert Hsi; apply le_Sn_0.

   apply le_S_n in Hsi.
   rewrite Nat.sub_succ.
   rewrite <- minus_Sn_m; [ idtac | assumption ].
   rewrite <- plus_n_Sm.
   simpl.
   remember (i - s) as x.
   rewrite <- Nat.sub_succ; subst x.
   rewrite <- minus_Sn_m; [ reflexivity | idtac ].
   rewrite <- plus_n_Sm in Hjsk.
   assumption.

  apply Nat.lt_le_incl; assumption.

  rewrite <- plus_n_Sm in Hjsk.
  apply Nat.lt_le_incl; assumption.
Qed.

Lemma nth_is_zero : ∀ (pol : polynomial (puiseux_series α)) q i j k sk tl,
  0 < q
  → 0 < sk
    → k = (j + sk * q)
      → Sorted fst_lt tl
        → (∀ hq αh, (hq, αh) ∈ tl
           → ∃ h sh, hq = Qnat h ∧ 0 < sh ∧ h = j + sh * q ∧ h < k)
            → S i mod q ≠ 0
              → (List.nth i
                  (make_char_pol f (S j) (List.map (term_of_point f pol) tl))
                  (fld_zero f)
                 .= f fld_zero f)%F.
Proof.
intros pol q i j k sk tl Hq Hsk Hk Hsort Hsh Himq.
destruct q; [ exfalso; revert Hq; apply lt_irrefl | clear Hq ].
destruct sk; [ exfalso; revert Hsk; apply lt_irrefl | clear Hsk ].
revert q i j sk k Hk Hsh Himq.
induction tl as [| t]; intros; [ destruct i; reflexivity | idtac ].
destruct t as (hq, αh); simpl.
unfold nofq; simpl.
assert ((hq, αh) ∈ [(hq, αh) … tl]) as H by (left; reflexivity).
apply Hsh in H.
destruct H as (h, (sh, (Hh, (Hsh₀, (Hhq, Hhk))))).
destruct sh; [ exfalso; revert Hsh₀; apply lt_irrefl | clear Hsh₀ ].
rewrite Hh; simpl.
rewrite Nat2Z.id.
rewrite Hhq in |- * at 1; simpl.
rewrite <- plus_Snm_nSm, minus_plus.
remember (q + sh * S q) as s.
destruct (lt_dec i s) as [Hlt| Hge].
 rewrite list_nth_pad_lt; [ reflexivity | assumption ].

 apply not_gt in Hge.
 remember Hge as H; clear HeqH.
 apply le_plus_minus in H.
 rewrite H, plus_comm, list_nth_plus_pad.
 remember (i - s) as is.
 destruct is.
  simpl.
  rewrite plus_0_r in H.
  subst i.
  simpl in Heqs.
  rewrite Heqs in Himq.
  rewrite <- plus_Sn_m in Himq.
  rewrite Nat.mod_add in Himq.
   rewrite Nat.mod_same in Himq.
    negation Himq.

    intros H; discriminate H.

   intros H; discriminate H.

  simpl.
  rewrite <- Nat.sub_succ in Heqis.
  destruct (eq_nat_dec i s) as [Heq| Hne].
   subst s.
   rewrite <- Heq, minus_diag in Heqis; discriminate Heqis.

   rewrite <- minus_Sn_m in Heqis.
    apply eq_add_S in Heqis.
    replace (S (q + sh * S q)) with (S sh * S q) by reflexivity.
    rewrite Hhq, <- plus_Sn_m.
    rewrite Heqs in Hge.
    apply le_n_S in Hge.
    rewrite <- plus_Sn_m, plus_comm, <- mult_succ_l in Hge.
    destruct tl as [| t]; [ destruct is; reflexivity | idtac ].
    rewrite Heqis, Heqs.
    rewrite plus_comm, mult_comm, plus_n_Sm.
    rewrite <- mult_succ_r, mult_comm.
    remember (List.map (term_of_point f pol) [t … tl]) as x.
    simpl in Heqx; subst x.
    rewrite nth_minus_char_pol_plus_cons.
     move Hk at bottom.
     eapply IHtl; try eapply Sorted_inv_1; try eassumption.
     intros hq₁ αh₁ Hhαh₁.
     destruct Hhαh₁ as [| Hhαh₁].
      subst t.
      eapply Hsh.
      right; left; reflexivity.

      eapply Hsh.
      right; right; eassumption.

     rewrite Heqs in Heqis.
     rewrite plus_comm, mult_comm, plus_n_Sm in Heqis.
     rewrite <- mult_succ_r, mult_comm in Heqis.
     apply eq_S in H.
     rewrite Heqs in H.
     rewrite plus_comm, mult_comm, plus_n_Sm in H.
     rewrite <- plus_Sn_m in H.
     remember (S q + S q * sh) as x.
     rewrite plus_comm, <- mult_succ_r, mult_comm in Heqx.
     subst x; omega.

     unfold term_of_point; remember (S sh) as x; simpl; subst x.
     rewrite <- Hhq.
     apply Sorted_inv_2 in Hsort.
     destruct Hsort as (Hsort, _).
     unfold fst_lt in Hsort; simpl in Hsort.
     rewrite Hh in Hsort; unfold nofq.
     destruct t as (h₁, αh₁).
     simpl in Hsort |- *.
     assert ((h₁, αh₁) ∈ [(hq, αh); (h₁, αh₁) … tl]) as H₁.
      right; left; reflexivity.

      apply Hsh in H₁.
      destruct H₁ as (h₂, (sh₂, (Hh₂, (Hsh₂, (Hhj₂, Hhk₂))))).
      rewrite Hh₂ in Hsort |- *.
      simpl.
      rewrite Nat2Z.id.
      unfold Qnat in Hsort.
      unfold Qlt in Hsort.
      simpl in Hsort.
      do 2 rewrite Zmult_1_r in Hsort.
      apply Nat2Z.inj_lt; assumption.

   apply not_eq_sym in Hne.
   apply le_neq_lt; assumption.
Qed.

Lemma minimise_slope_lt_seg : ∀ pt₁ pt₂ pt₃ pts ms₂,
  Sorted fst_lt [pt₁; pt₂; pt₃ … pts]
  → minimise_slope pt₁ pt₃ pts = ms₂
    → HdRel fst_lt pt₂ (seg ms₂).
Proof.
intros pt₁ pt₂ pt₃ pts ms₂ Hsort Hms₂.
revert pt₁ pt₂ pt₃ ms₂ Hsort Hms₂.
induction pts as [| pt₄]; intros.
 subst ms₂; constructor.

 simpl in Hms₂.
 remember (minimise_slope pt₁ pt₄ pts) as ms₄.
 symmetry in Heqms₄.
 remember (slope_expr pt₁ pt₃ ?= slope ms₄)%Q as c.
 symmetry in Heqc.
 destruct c.
  subst ms₂; simpl.
  constructor.
  apply Sorted_inv_2 in Hsort.
  destruct Hsort as (_, Hsort).
  apply Sorted_inv_2 in Hsort.
  destruct Hsort; assumption.

  subst ms₂; constructor.

  move Hms₂ at top; subst ms₄.
  eapply IHpts; [ idtac | eassumption ].
  eapply Sorted_minus_3rd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Lemma minimise_slope_seg_sorted : ∀ pt₁ pt₂ pts ms₁,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms₁
    → Sorted fst_lt (seg ms₁).
Proof.
intros pt₁ pt₂ pts ms₁ Hsort Hms₁.
revert pt₁ pt₂ ms₁ Hsort Hms₁.
induction pts as [| pt₃]; intros.
 subst ms₁; constructor.

 simpl in Hms₁.
 remember (minimise_slope pt₁ pt₃ pts) as ms₂.
 symmetry in Heqms₂.
 remember (slope_expr pt₁ pt₂ ?= slope ms₂)%Q as c.
 destruct c.
  subst ms₁; simpl.
  constructor.
   eapply IHpts; [ idtac | eassumption ].
   eapply Sorted_minus_2nd; [ idtac | eassumption ].
   intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

   eapply minimise_slope_lt_seg; eassumption.

  subst ms₁; constructor.

  subst ms₂.
  eapply IHpts; [ idtac | eassumption ].
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Lemma edge_pts_sorted : ∀ n pts hs,
  Sorted fst_lt pts
  → hs ∈ next_ch_points n pts
    → Sorted fst_lt (edge hs).
Proof.
intros n pts hs Hsort Hhs.
revert pts hs Hsort Hhs.
induction n; intros; [ contradiction | simpl in Hhs ].
destruct pts as [| pt₁]; [ contradiction | idtac ].
destruct pts as [| pt₂].
 destruct Hhs; [ subst hs; constructor | contradiction ].

 destruct Hhs as [Hhs| Hhs].
  subst hs; simpl.
  eapply minimise_slope_seg_sorted; [ eassumption | reflexivity ].

  eapply IHn; [ idtac | eassumption ].
  eapply minimise_slope_sorted; [ eassumption | reflexivity ].
Qed.

Lemma minimise_slope_edge_sorted : ∀ pt₁ pt₂ pts ms₁ hs n,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms₁
    → hs ∈ next_ch_points n [end_pt ms₁ … rem_pts ms₁]
      → Sorted fst_lt (edge hs).
Proof.
intros pt₁ pt₂ pts ms₁ hs n Hsort Hms₁ Hhs.
revert pt₁ pt₂ ms₁ hs n Hsort Hms₁ Hhs.
induction pts as [| pt₃]; intros.
 subst ms₁; simpl in Hhs.
 destruct n; [ contradiction | idtac ].
 simpl in Hhs.
 destruct Hhs; [ subst hs; constructor | contradiction ].

 simpl in Hms₁.
 remember (minimise_slope pt₁ pt₃ pts) as ms₃.
 symmetry in Heqms₃.
 remember (slope_expr pt₁ pt₂ ?= slope ms₃)%Q as c.
 destruct c.
  subst ms₁.
  simpl in Hhs.
  eapply IHpts; try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

  subst ms₁; simpl in Hhs.
  eapply edge_pts_sorted; [ idtac | eassumption ].
  eapply Sorted_inv_1; eassumption.

  move Hms₁ at top; subst ms₃.
  eapply IHpts; try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Lemma minimise_slope_end_lt : ∀ pt₁ pt₂ pt₃ pt₄ pts pts₁ ms₁,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms₁
    → end_pt ms₁ = pt₃
      → rem_pts ms₁ = [pt₄ … pts₁]
        → (fst pt₃ < fst pt₄)%Q.
Proof.
fix IHpts 5.
intros pt₁ pt₂ pt₃ pt₄ pts pts₁ ms₁ Hsort Hms₁ Hend₁ Hrem₁.
destruct pts as [| pt₅].
 subst ms₁; simpl in Hrem₁; discriminate Hrem₁.

 simpl in Hms₁.
 remember (minimise_slope pt₁ pt₅ pts) as ms₂.
 symmetry in Heqms₂.
 remember (slope_expr pt₁ pt₂ ?= slope ms₂)%Q as c.
 symmetry in Heqc.
 destruct c.
  subst ms₁; simpl in Hend₁, Hrem₁.
  eapply IHpts with (pt₂ := pt₅); try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

  subst ms₁; simpl in Hend₁, Hrem₁.
  subst pt₂.
  injection Hrem₁; clear Hrem₁; intros; subst pt₄ pts₁.
  apply Sorted_inv_1 in Hsort.
  apply Sorted_inv_2 in Hsort.
  destruct Hsort; assumption.

  subst ms₁.
  eapply IHpts with (pt₂ := pt₅); try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Lemma minimise_slope_rem_lt : ∀ pt₁ pt₂ pt₃ pts pts₁ ms₁,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms₁
    → rem_pts ms₁ = [pt₃ … pts₁]
      → HdRel fst_lt pt₃ pts₁.
Proof.
intros pt₁ pt₂ pt₃ pts pts₁ ms₁ Hsort Hms₁ Hrem₁.
revert pt₁ pt₂ pt₃ pts₁ ms₁ Hsort Hms₁ Hrem₁.
induction pts as [| pt₄]; intros.
 subst ms₁; discriminate Hrem₁.

 simpl in Hms₁.
 remember (minimise_slope pt₁ pt₄ pts) as ms₂.
 symmetry in Heqms₂.
 remember (slope_expr pt₁ pt₂ ?= slope ms₂)%Q as c.
 symmetry in Heqc.
 destruct c.
  subst ms₁; simpl in Hrem₁.
  eapply IHpts; try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.

  subst ms₁; simpl in Hrem₁.
  injection Hrem₁; clear Hrem₁; intros; subst pt₄ pts₁.
  apply Sorted_inv_1 in Hsort.
  apply Sorted_inv_1 in Hsort.
  apply Sorted_inv in Hsort.
  destruct Hsort; assumption.

  move Hms₁ at top; subst ms₂.
  eapply IHpts; try eassumption.
  eapply Sorted_minus_2nd; [ idtac | eassumption ].
  intros x y z H₁ H₂; eapply Qlt_trans; eassumption.
Qed.

Lemma minimise_slope_oth_pts_sorted : ∀ pt₁ pt₂ pts hsl ns ms₁ n,
  Sorted fst_lt [pt₁; pt₂ … pts]
  → minimise_slope pt₁ pt₂ pts = ms₁
    → next_ch_points n [end_pt ms₁ … rem_pts ms₁] = hsl
      → ns ∈ list_map_pairs newton_segment_of_pair hsl
        → Sorted fst_lt (oth_pts ns).
Proof.
intros pt₁ pt₂ pts hsl ns ms₁ n Hsort Hms₁ Hnp Hns.
revert pt₁ pt₂ pts ns ms₁ n Hsort Hms₁ Hnp Hns.
induction hsl as [| hs₁]; intros; [ contradiction | idtac ].
simpl in Hns.
destruct hsl as [| hs₂]; [ contradiction | idtac ].
destruct Hns as [Hns| Hns].
 subst ns; simpl.
 eapply minimise_slope_edge_sorted with (n := n); try eassumption.
 rewrite Hnp; left; reflexivity.

 destruct n; [ discriminate Hnp | simpl in Hnp ].
 remember (rem_pts ms₁) as pts₁.
 symmetry in Heqpts₁.
 destruct pts₁ as [| pt₃]; [ discriminate Hnp | idtac ].
 injection Hnp; clear Hnp; intros Hnp; intros; subst hs₁.
 remember (minimise_slope (end_pt ms₁) pt₃ pts₁) as ms₂.
 symmetry in Heqms₂.
 eapply IHhsl with (pt₁ := end_pt ms₁); try eassumption.
 constructor.
  constructor.
   apply minimise_slope_sorted in Hms₁; [ idtac | assumption ].
   rewrite Heqpts₁ in Hms₁.
   apply Sorted_inv_2 in Hms₁.
   destruct Hms₁ as (_, Hms₁).
   eapply Sorted_inv_1; eassumption.

   eapply minimise_slope_rem_lt; eassumption.

  constructor.
  eapply minimise_slope_end_lt; try eassumption; reflexivity.
Qed.

Lemma Sorted_app : ∀ α f l (x : α),
  Sorted f l
  → (∀ y, y ∈ l → f y x)
    → Sorted f (l ++ [x]).
Proof.
clear; intros α f l x Hs Hf.
induction l as [| z]; [ constructor; constructor | simpl ].
apply Sorted_inv in Hs.
destruct Hs as (Hs, Hr).
apply IHl in Hs.
 constructor; [ assumption | idtac ].
 destruct l as [| t].
  constructor; apply Hf; left; reflexivity.

  constructor; apply HdRel_inv in Hr; assumption.

 intros y Hy.
 apply Hf; right; assumption.
Qed.

Lemma oth_fin_pts_sorted : ∀ pol ns,
  ns ∈ newton_segments f pol
  → Sorted fst_lt (oth_pts ns ++ [fin_pt ns]).
Proof.
intros pol ns Hns.
remember Hns as Hns_v; clear HeqHns_v.
unfold newton_segments in Hns.
remember (points_of_ps_polynom f pol) as pts.
apply points_of_polyn_sorted in Heqpts.
remember (lower_convex_hull_points pts) as hsl.
unfold lower_convex_hull_points in Heqhsl.
rename Heqhsl into Hnp.
symmetry in Hnp.
remember (length pts) as n; clear Heqn.
induction hsl as [| hs₁]; intros; [ contradiction | idtac ].
destruct hsl as [| hs₂]; [ contradiction | idtac ].
rewrite list_map_pairs_cons_cons in Hns.
apply Sorted_app.
 destruct Hns as [Hns| Hns].
  subst ns; simpl.
  eapply edge_pts_sorted with (n := n); [ eassumption | idtac ].
  rewrite Hnp; left; reflexivity.

  destruct n; [ discriminate Hnp | simpl in Hnp ].
  destruct pts as [| pt₁]; [ discriminate Hnp | idtac ].
  destruct pts as [| pt₂]; [ discriminate Hnp | idtac ].
  injection Hnp; clear Hnp; intros Hnp; intros; subst hs₁.
  remember (minimise_slope pt₁ pt₂ pts) as ms₁.
  symmetry in Heqms₁.
  eapply minimise_slope_oth_pts_sorted; eassumption.

 intros (hq, αh) Hh.
 eapply hq_lt_kq; try eassumption.
 symmetry; apply surjective_pairing.
Qed.

Close Scope nat_scope.

(* [Walker, p. 100] « ... » *)
Theorem characteristic_polynomial_is_in_x_power_q : ∀ pol ns cpol j αj k αk m,
  ns ∈ newton_segments f pol
  → cpol = characteristic_polynomial f pol ns
    → (Qnat j, αj) = ini_pt ns
      → (Qnat k, αk) = fin_pt ns
        → m = series_list_com_den (bl pol)
          → ∃ mj mk, αj == mj # m ∧ αk == mk # m
            ∧ ∃ p q, Z.gcd p (Z.of_nat q) = 1
              ∧ (∃ sk, k = j + sk * q)%nat
              ∧ (∀ h αh, (Qnat h, αh) ∈ oth_pts ns
                 → ∃ mh sh, αh == mh # m ∧ h = j + sh * q)%nat
              ∧ is_polynomial_in_x_power_q cpol q.
Proof.
intros pol ns cpol j αj k αk m Hns Hcpol Hj Hk Heqm.
remember Hns as H; clear HeqH.
eapply h_is_j_plus_sq in H; try eassumption.
bbb.
destruct H as (mj, (mk, (Hmj, (Hmk, (p, (q, (Hgcd, (Hqjk, Hmh)))))))).
exists mj, mk.
split; [ assumption | idtac ].
split; [ assumption | idtac ].
exists p, q.
split; [ assumption | idtac ].
split; [ assumption | idtac ].
split; [ assumption | idtac ].
remember Hns as H; clear HeqH.
apply ini_fin_ns_in_init_pts in H.
destruct H as (Hini, Hfin).
eapply pt_absc_is_nat in Hini; [ idtac | reflexivity ].
eapply pt_absc_is_nat in Hfin; [ idtac | reflexivity ].
rename j into jz.
rename k into kz.
unfold is_polynomial_in_x_power_q.
intros i c Himq Hc.
subst cpol.
unfold characteristic_polynomial in Hc; simpl in Hc.
rewrite minus_diag in Hc; simpl in Hc.
destruct i.
 exfalso; apply Himq.
 apply Nat.mod_0_l.
 apply Pos2Nat_ne_0.

 rewrite <- Hj, <- Hk in Hc; simpl in Hc.
 unfold nofq in Hc; simpl in Hc.
 destruct Hqjk as (sk, Hqjk).
 rewrite Hqjk in Hc; simpl in Hc.
 rename q into qp.
 remember (Pos.to_nat qp) as q.
 destruct q.
  pose proof (Pos2Nat.is_pos qp) as H.
  rewrite <- Heqq in H; apply lt_irrefl in H; contradiction.

  rename sk into skp.
  remember (Pos.to_nat skp) as sk.
  destruct sk.
   pose proof (Pos2Nat.is_pos skp) as H.
   rewrite <- Heqsk in H; apply lt_irrefl in H; contradiction.

   subst c.
   apply
    nth_is_zero
     with (q := Pos.to_nat qp) (k := Z.to_nat kz) (sk := Pos.to_nat skp).
    apply Pos2Nat.is_pos.

    apply Pos2Nat.is_pos.

    subst kz.
    rewrite Z2Nat.inj_add; try apply Pos2Z.is_nonneg.
     rewrite Z2Nat.inj_mul; try apply Pos2Z.is_nonneg.
     reflexivity.

     unfold newton_segments in Hns.
     remember (points_of_ps_polynom f pol) as pts.
     remember Heqpts as H; clear HeqH.
     symmetry in H.
     apply pt_absc_is_nat with (pt := ini_pt ns) in H.
      rewrite <- Hj in H; simpl in H.
      unfold Qnat in H.
      injection H; clear H; intros H.
      rewrite H.
      apply Nat2Z.is_nonneg.

      apply ini_fin_ns_in_init_pts in Hns.
      destruct Hns; assumption.

    rewrite Pos2Z.inj_mul, <- Hqjk, Hk.
    eapply oth_fin_pts_sorted; eassumption.

    intros hq αh Hhαh.
    apply List.in_app_or in Hhαh.
    destruct Hhαh as [Hhαh| Hhαh].
     assert ((inject_Z (Qnum hq), αh) ∈ oth_pts ns) as Hin.
      unfold newton_segments in Hns.
      remember (points_of_ps_polynom f pol) as pts.
      symmetry in Heqpts.
      apply pt_absc_is_nat with (pt := (hq, αh)) in Heqpts.
       simpl in Heqpts.
       move Heqpts at bottom.
       rewrite Heqpts in Hhαh.
       unfold Qnat in Hhαh.
       rewrite Z2Nat.id in Hhαh.
        assumption.

        rewrite Heqpts; simpl.
        apply Nat2Z.is_nonneg.

       eapply oth_pts_in_init_pts; eassumption.

      apply Hmh in Hin.
      destruct Hin as (mh, (sh, (Hαh, Hhq))).
      exists (Z.to_nat (Qnum hq)), (Pos.to_nat sh).
      split.
       replace hq with (fst (hq, αh)) by reflexivity.
       unfold newton_segments in Hns.
       remember (points_of_ps_polynom f pol) as pts.
       symmetry in Heqpts.
       eapply pt_absc_is_nat; [ eassumption | idtac ].
       eapply oth_pts_in_init_pts; eassumption.

       split; [ apply Pos2Nat.is_pos | idtac ].
       split.
        rewrite Hhq.
        rewrite Z2Nat.inj_add.
         rewrite Z2Nat.inj_mul; try apply Zle_0_pos.
         simpl; rewrite <- Heqq.
         reflexivity.

         unfold newton_segments in Hns.
         remember (points_of_ps_polynom f pol) as pts.
         symmetry in Heqpts.
         apply pt_absc_is_nat with (pt := ini_pt ns) in Heqpts.
          rewrite <- Hj in Heqpts.
          simpl in Heqpts.
          move Heqpts at bottom.
          unfold inject_Z, Qnat in Heqpts.
          injection Heqpts; clear Heqpts; intros H; rewrite H.
          apply Zle_0_nat.

          apply ini_fin_ns_in_init_pts; assumption.

         apply Zle_0_pos.

        eapply h_lt_k; try eassumption.
         unfold newton_segments in Hns.
         remember (points_of_ps_polynom f pol) as pts.
         symmetry in Heqpts.
         apply pt_absc_is_nat with (pt := (hq, αh)) in Heqpts.
          assumption.

          eapply oth_pts_in_init_pts; try eassumption.

         unfold newton_segments in Hns.
         remember (points_of_ps_polynom f pol) as pts.
         symmetry in Heqpts.
         apply pt_absc_is_nat with (pt := fin_pt ns) in Heqpts.
          rewrite <- Hk in Heqpts.
          assumption.

          apply ini_fin_ns_in_init_pts in Hns.
          destruct Hns; assumption.

     destruct Hhαh as [Hhαh| ]; [ idtac | contradiction ].
bbb.

intros pol ns cpol j αj k αk m Hns Hcpol Hj Hk Heqm.
remember Hns as H; clear HeqH.
eapply h_is_j_plus_sq in H; try eassumption.
destruct H as (mj, (mk, (Hmj, (Hmk, (p, (q, (Hgcd, (Hqjk, Hmh)))))))).
exists mj, mk.
split; [ assumption | idtac ].
split; [ assumption | idtac ].
exists p, q.
split; [ assumption | idtac ].
split; [ assumption | idtac ].
split; [ assumption | idtac ].
remember Hns as H; clear HeqH.
apply ini_fin_ns_in_init_pts in H.
destruct H as (Hini, Hfin).
eapply pt_absc_is_nat in Hini; [ idtac | reflexivity ].
eapply pt_absc_is_nat in Hfin; [ idtac | reflexivity ].
rename j into jz.
rename k into kz.
unfold is_polynomial_in_x_power_q.
intros i c Himq Hc.
subst cpol.
unfold characteristic_polynomial in Hc; simpl in Hc.
rewrite minus_diag in Hc; simpl in Hc.
destruct i.
 exfalso; apply Himq.
 apply Nat.mod_0_l.
 apply Pos2Nat_ne_0.

 rewrite <- Hj, <- Hk in Hc; simpl in Hc.
 unfold nofq in Hc; simpl in Hc.
 destruct Hqjk as (sk, Hqjk).
 rewrite Hqjk in Hc; simpl in Hc.
(*
 rewrite Z2Nat.inj_add in Hc; simpl in Hc.
  rewrite Pos2Nat.inj_mul in Hc.
  remember (Z.to_nat jz) as j.
*)
  rename q into qp.
  remember (Pos.to_nat qp) as q.
  destruct q.
   pose proof (Pos2Nat.is_pos qp) as H.
   rewrite <- Heqq in H; apply lt_irrefl in H; contradiction.

   rename sk into skp.
   remember (Pos.to_nat skp) as sk.
   destruct sk.
    pose proof (Pos2Nat.is_pos skp) as H.
    rewrite <- Heqsk in H; apply lt_irrefl in H; contradiction.

    subst c.
bbb.
    eapply nth_is_zero; try reflexivity; try assumption; try apply lt_0_Sn.
    rewrite Pos2Z.inj_mul, <- Hqjk, Hk.
     eapply oth_fin_pts_sorted; eassumption.

     intros hq αh Hhαh.
     assert ((inject_Z (Qnum hq), αh) ∈ oth_pts ns) as Hin.
bbb.
      unfold newton_segments in Hns.
      remember (points_of_ps_polynom f pol) as pts.
      symmetry in Heqpts.
      apply pt_absc_is_nat with (pt := (hq, αh)) in Heqpts.
       simpl in Heqpts.
       move Heqpts at bottom.
       rewrite Heqpts in Hhαh.
       unfold Qnat in Hhαh.
      apply List.in_app_or in Hhαh.
      destruct Hhαh as [Hhαh| Hhαh].
       rewrite Z2Nat.id in Hhαh.
        assumption.

        rewrite Heqpts; simpl.
        apply Nat2Z.is_nonneg.

       destruct Hhαh as [Hhαh| ]; [ idtac | contradiction ].
bbb.

       rewrite Z2Nat.id in Hhαh; [ assumption | idtac ].
       rewrite Heqpts; simpl.
       apply Zle_0_nat.

       eapply oth_pts_in_init_pts; eassumption.

      apply Hmh in Hin.
      destruct Hin as (mh, (sh, (Hαh, Hhq))).
      exists (Z.to_nat (Qnum hq)), (Pos.to_nat sh).
      split.
       replace hq with (fst (hq, αh)) by reflexivity.
       unfold newton_segments in Hns.
       remember (points_of_ps_polynom f pol) as pts.
       symmetry in Heqpts.
       eapply pt_absc_is_nat; [ eassumption | idtac ].
       eapply oth_pts_in_init_pts; eassumption.

       split; [ apply Pos2Nat.is_pos | idtac ].
       split.
        rewrite Hhq, Heqj, Heqq.
        rewrite Z2Nat.inj_add.
         rewrite Z2Nat.inj_mul; try apply Zle_0_pos; reflexivity.

         unfold newton_segments in Hns.
         remember (points_of_ps_polynom f pol) as pts.
         symmetry in Heqpts.
         apply pt_absc_is_nat with (pt := ini_pt ns) in Heqpts.
          rewrite <- Hj in Heqpts.
          simpl in Heqpts.
          move Heqpts at bottom.
          unfold inject_Z, Qnat in Heqpts.
          injection Heqpts; clear Heqpts; intros H; rewrite H.
          apply Zle_0_nat.

          apply ini_fin_ns_in_init_pts; assumption.

         apply Zle_0_pos.

        rewrite Heqj, Heqsk, Heqq.
        rewrite <- Pos2Nat.inj_mul.
        simpl in Hqjk.
        rewrite <- Z2Nat.inj_pos.
        rewrite <- Z2Nat.inj_add.
         rewrite <- Hqjk.
         eapply h_lt_k; try eassumption.
          unfold newton_segments in Hns.
          remember (points_of_ps_polynom f pol) as pts.
          symmetry in Heqpts.
          apply pt_absc_is_nat with (pt := (hq, αh)) in Heqpts.
           assumption.

           eapply oth_pts_in_init_pts; eassumption.

          unfold newton_segments in Hns.
          remember (points_of_ps_polynom f pol) as pts.
          symmetry in Heqpts.
          apply pt_absc_is_nat with (pt := (inject_Z kz, αk)) in Heqpts.
           assumption.

           rewrite Hk.
           apply ini_fin_ns_in_init_pts; assumption.

         unfold newton_segments in Hns.
         remember (points_of_ps_polynom f pol) as pts.
         symmetry in Heqpts.
         apply pt_absc_is_nat with (pt := (inject_Z jz, αj)) in Heqpts.
          simpl in Heqpts.
          unfold Qnat in Heqpts.
          move Heqpts at bottom.
          unfold inject_Z in Heqpts.
          injection Heqpts; clear Heqpts; intros Hjz; rewrite Hjz.
          apply Zle_0_nat.

          rewrite Hj.
          apply ini_fin_ns_in_init_pts; assumption.

         apply Zle_0_pos.

  unfold newton_segments in Hns.
  remember (points_of_ps_polynom f pol) as pts.
  symmetry in Heqpts.
  apply pt_absc_is_nat with (pt := (inject_Z jz, αj)) in Heqpts.
   simpl in Heqpts.
   unfold Qnat in Heqpts.
   move Heqpts at bottom.
   unfold inject_Z in Heqpts.
   injection Heqpts; clear Heqpts; intros Hjz; rewrite Hjz.
   apply Zle_0_nat.

   rewrite Hj.
   apply ini_fin_ns_in_init_pts; assumption.

  apply Zle_0_pos.
qed.

End theorems.
