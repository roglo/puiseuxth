(* Puiseux.v *)

Require Import Utf8.
Require Import QArith.

Require Import Misc.
Require Import Slope_base.
Require Import Qbar.
Require Import Field.
Require Import Fpolynomial.
Require Import Newton.
Require Import ConvexHull.
Require Import Puiseux_series.
Require Import Ps_add.
Require Import Ps_div.
Require Import PSpolynomial.
Require Import Puiseux_base.
Require Import AlgCloCharPol.
Require Import CharactPolyn.
Require Import F1Eq.
Require Import PosOrder.
Require Import F1Prop.

Set Implicit Arguments.

Definition eq_pt pt₁ pt₂ := fst pt₁ == fst pt₂ ∧ snd pt₁ == snd pt₂.
Definition eq_list_pt := List.Forall2 eq_pt.
Definition eq_ns ns₁ ns₂ :=
  γ ns₁ == γ ns₂ ∧ β ns₁ == β ns₂ ∧ eq_pt (ini_pt ns₁) (ini_pt ns₂)
  ∧ eq_list_pt (oth_pts ns₁) (oth_pts ns₂) ∧ eq_pt (fin_pt ns₁) (fin_pt ns₂).
Definition eq_list_ns := List.Forall2 eq_ns.
Definition eq_hs hs₁ hs₂ :=
  eq_pt (vert hs₁) (vert hs₂) ∧ eq_list_pt (edge hs₁) (edge hs₂).
Definition eq_list_hs := List.Forall2 eq_hs.

Definition eq_min_sl ms₁ ms₂ :=
  slope ms₁ == slope ms₂ ∧ eq_pt (end_pt ms₁) (end_pt ms₂)
  ∧ eq_list_pt (seg ms₁) (seg ms₂) ∧ eq_list_pt (rem_pts ms₁) (rem_pts ms₂).

Delimit Scope pt_scope with pt.
Notation "a = b" := (eq_pt a b) : pt_scope.

Delimit Scope list_pt_scope with pts.
Notation "a = b" := (eq_list_pt a b) : list_pt_scope.

Delimit Scope ns_scope with ns.
Notation "a = b" := (eq_ns a b) : ns_scope.

Delimit Scope list_ns_scope with nsl.
Notation "a = b" := (eq_list_ns a b) : list_ns_scope.

Delimit Scope hs_scope with hs.
Notation "a = b" := (eq_hs a b) : hs_scope.

Delimit Scope list_hs_scope with hsl.
Notation "a = b" := (eq_list_hs a b) : list_hs_scope.

Delimit Scope ms_scope with ms.
Notation "a = b" := (eq_min_sl a b) : ms_scope.

Lemma fold_eq_list_pt : List.Forall2 eq_pt = eq_list_pt.
Proof. reflexivity. Qed.

Lemma fold_eq_list_ns : List.Forall2 eq_ns = eq_list_ns.
Proof. reflexivity. Qed.

Lemma fold_eq_list_hs : List.Forall2 eq_hs = eq_list_hs.
Proof. reflexivity. Qed.

Theorem eq_pt_refl : reflexive _ eq_pt.
Proof. intros; split; reflexivity. Qed.

Theorem eq_pt_sym : symmetric _ eq_pt.
Proof.
intros pt₁ pt₂ H.
destruct H; split; symmetry; assumption.
Qed.

Theorem eq_pt_trans : transitive _ eq_pt.
Proof.
intros pt₁ pt₂ pt₃ H₁ H₂.
destruct H₁, H₂.
split; etransitivity; eassumption.
Qed.

Add Parametric Relation : (Q * Q) eq_pt
 reflexivity proved by eq_pt_refl
 symmetry proved by eq_pt_sym
 transitivity proved by eq_pt_trans
 as eq_pt_rel.

Add Parametric Morphism : (@pair Q Q)
  with signature Qeq ==> Qeq ==> eq_pt
  as pair_Q_morph.
Proof.
intros a b Hab c d Hcd.
split; simpl; assumption.
Qed.

Theorem eq_list_pt_refl : reflexive _ eq_list_pt.
Proof.
intros pts.
induction pts; constructor; [ reflexivity | assumption ].
Qed.

Theorem eq_list_pt_sym : symmetric _ eq_list_pt.
Proof.
intros pts₁ pts₂ Heq.
revert pts₂ Heq.
induction pts₁ as [| pt₁]; intros.
 destruct pts₂; [ constructor | inversion Heq ].

 destruct pts₂ as [| pt₂]; [ inversion Heq | idtac ].
 inversion Heq; subst.
 constructor; [ destruct H2; split; symmetry; assumption | idtac ].
 apply IHpts₁; assumption.
Qed.

Theorem eq_list_pt_trans : transitive _ eq_list_pt.
Proof.
intros pts₁ pts₂ pts₃ H₁ H₂.
revert pts₁ pts₃ H₁ H₂.
induction pts₂ as [| pt₂]; intros.
 inversion H₁; subst.
 inversion H₂; subst.
 constructor.

 destruct pts₁ as [| pt₁]; [ inversion H₁ | idtac ].
 destruct pts₃ as [| pt₃]; [ inversion H₂ | idtac ].
 inversion H₁; subst.
 inversion H₂; subst.
 constructor.
  destruct H2, H3.
  split; etransitivity; eassumption.

  apply IHpts₂; assumption.
Qed.

Add Parametric Relation : (list (Q * Q)) eq_list_pt
 reflexivity proved by eq_list_pt_refl
 symmetry proved by eq_list_pt_sym
 transitivity proved by eq_list_pt_trans
 as eq_list_pt_rel.

Add Parametric Morphism α (R : ring α) : (@points_of_ps_lap_gen _ R)
  with signature eq ==> @lap_eq _ (ps_ring R) ==> eq_list_pt
  as points_of_ps_lap_gen_morph.
Proof.
intros pow la lb Hlab.
unfold points_of_ps_lap_gen; simpl.
revert pow lb Hlab.
induction la as [| a]; intros; simpl.
 revert pow.
 induction lb as [| b]; intros; [ reflexivity | simpl ].
 apply lap_eq_nil_cons_inv in Hlab.
 destruct Hlab as (Hb, Hlb).
 simpl in Hb.
 apply order_inf in Hb; rewrite Hb.
 apply IHlb; assumption.

 destruct lb as [| b]; simpl.
  apply lap_eq_cons_nil_inv in Hlab.
  destruct Hlab as (Ha, Hla).
  simpl in Ha.
  apply order_inf in Ha; rewrite Ha; simpl.
  revert Hla; clear; intros.
  revert pow.
  induction la as [| a]; intros; [ reflexivity | simpl ].
  apply lap_eq_cons_nil_inv in Hla.
  destruct Hla as (Ha, Hla).
  simpl in Ha.
  apply order_inf in Ha; rewrite Ha.
  apply IHla; assumption.

  apply lap_eq_cons_inv in Hlab.
  destruct Hlab as (Hab, Hlab).
  simpl in Hab.
  apply order_morph in Hab.
  remember (order a) as oa eqn:Hoa .
  remember (order b) as ob eqn:Hob .
  symmetry in Hoa, Hob.
  destruct oa as [va| ].
   destruct ob as [vb| ]; [ idtac | inversion Hab ].
   apply Qbar.qfin_inj in Hab.
   constructor; [ rewrite Hab; reflexivity | idtac ].
   do 2 rewrite fold_qpower_list.
   rewrite IHla; [ reflexivity | assumption ].

   destruct ob as [vb| ]; [ inversion Hab | idtac ].
   apply IHla; assumption.
Qed.

Add Parametric Morphism α (R : ring α) : (@points_of_ps_polynom _ R)
  with signature @ps_pol_eq _ R ==> eq_list_pt
  as points_of_ps_polynom_morph.
Proof.
intros Pa Pb HP.
unfold points_of_ps_polynom.
unfold points_of_ps_lap.
rewrite HP; reflexivity.
Qed.

Theorem eq_ns_refl : reflexive _ eq_ns.
Proof.
intros ns.
unfold eq_ns.
split; [ reflexivity | idtac ].
split; [ reflexivity | idtac ].
split; [ reflexivity | idtac ].
split; [ reflexivity | idtac ].
split; reflexivity.
Qed.

Theorem eq_ns_sym : symmetric _ eq_ns.
Proof.
intros ns₁ ns₂ H.
unfold eq_ns in H; unfold eq_ns.
destruct H as (H₁, (H₂, (H₃, (H₄, H₅)))).
split; [ symmetry; assumption | idtac ].
split; [ symmetry; assumption | idtac ].
split; [ symmetry; assumption | idtac ].
split; symmetry; assumption.
Qed.

Theorem eq_ns_trans : transitive _ eq_ns.
Proof.
intros ns₁ ns₂ ns₃ H I.
unfold eq_ns in H, I; unfold eq_ns.
destruct H as (H₁, (H₂, (H₃, (H₄, H₅)))).
destruct I as (I₁, (I₂, (I₃, (I₄, I₅)))).
split; [ etransitivity; eassumption | idtac ].
split; [ etransitivity; eassumption | idtac ].
split; [ etransitivity; eassumption | idtac ].
split; etransitivity; eassumption.
Qed.

Add Parametric Relation : newton_segment eq_ns
 reflexivity proved by eq_ns_refl
 symmetry proved by eq_ns_sym
 transitivity proved by eq_ns_trans
 as eq_ns_rel.

Theorem eq_list_ns_refl : reflexive _ eq_list_ns.
Proof.
intros nsl.
induction nsl; constructor; [ reflexivity | assumption ].
Qed.

Theorem eq_list_ns_sym : symmetric _ eq_list_ns.
Proof.
intros nsl₁ nsl₂ Heq.
revert nsl₂ Heq.
induction nsl₁ as [| ns₁]; intros.
 destruct nsl₂; [ constructor | inversion Heq ].

 destruct nsl₂ as [| ns₂]; [ inversion Heq | idtac ].
 inversion Heq; subst.
 constructor; [ symmetry; assumption | idtac ].
 apply IHnsl₁; assumption.
Qed.

Theorem eq_list_ns_trans : transitive _ eq_list_ns.
Proof.
intros nsl₁ nsl₂ nsl₃ H₁ H₂.
revert nsl₁ nsl₃ H₁ H₂.
induction nsl₂ as [| ns₂]; intros.
 inversion H₁; subst.
 inversion H₂; subst.
 constructor.

 destruct nsl₁ as [| ns₁]; [ inversion H₁ | idtac ].
 destruct nsl₃ as [| ns₃]; [ inversion H₂ | idtac ].
 inversion H₁; subst.
 inversion H₂; subst.
 constructor; [ etransitivity; eassumption | apply IHnsl₂; assumption ].
Qed.

Add Parametric Relation : (list newton_segment) eq_list_ns
 reflexivity proved by eq_list_ns_refl
 symmetry proved by eq_list_ns_sym
 transitivity proved by eq_list_ns_trans
 as eq_list_ns_rel.

Theorem eq_hs_refl : reflexive _ eq_hs.
Proof.
intros hs.
unfold eq_hs.
split; reflexivity.
Qed.

Theorem eq_hs_sym : symmetric _ eq_hs.
Proof.
intros hs₁ hs₂ H.
unfold eq_hs in H; unfold eq_hs.
destruct H as (H₁, H₂).
split; symmetry; assumption.
Qed.

Theorem eq_hs_trans : transitive _ eq_hs.
Proof.
intros hs₁ hs₂ hs₃ H I.
unfold eq_hs in H, I; unfold eq_hs.
destruct H as (H₁, H₂).
destruct I as (I₁, I₂).
split; etransitivity; eassumption.
Qed.

Add Parametric Relation : hull_seg eq_hs
 reflexivity proved by eq_hs_refl
 symmetry proved by eq_hs_sym
 transitivity proved by eq_hs_trans
 as eq_hs_rel.

Theorem eq_list_hs_refl : reflexive _ eq_list_hs.
Proof.
intros hsl.
induction hsl; constructor; [ reflexivity | assumption ].
Qed.

Theorem eq_list_hs_sym : symmetric _ eq_list_hs.
Proof.
intros hsl₁ hsl₂ Heq.
revert hsl₂ Heq.
induction hsl₁ as [| hs₁]; intros.
 destruct hsl₂; [ constructor | inversion Heq ].

 destruct hsl₂ as [| hs₂]; [ inversion Heq | idtac ].
 inversion Heq; subst.
 constructor; [ symmetry; assumption | idtac ].
 apply IHhsl₁; assumption.
Qed.

Theorem eq_list_hs_trans : transitive _ eq_list_hs.
Proof.
intros hsl₁ hsl₂ hsl₃ H₁ H₂.
revert hsl₁ hsl₃ H₁ H₂.
induction hsl₂ as [| hs₂]; intros.
 inversion H₁; subst.
 inversion H₂; subst.
 constructor.

 destruct hsl₁ as [| hs₁]; [ inversion H₁ | idtac ].
 destruct hsl₃ as [| hs₃]; [ inversion H₂ | idtac ].
 inversion H₁; subst.
 inversion H₂; subst.
 constructor; [ etransitivity; eassumption | apply IHhsl₂; assumption ].
Qed.

Add Parametric Relation : (list hull_seg) eq_list_hs
 reflexivity proved by eq_list_hs_refl
 symmetry proved by eq_list_hs_sym
 transitivity proved by eq_list_hs_trans
 as eq_list_hs_rel.

Theorem eq_ms_refl : reflexive _ eq_min_sl.
Proof.
intros ms.
unfold eq_min_sl.
split; [ reflexivity | idtac ].
split; [ reflexivity | idtac ].
split; reflexivity.
Qed.

Theorem eq_ms_sym : symmetric _ eq_min_sl.
Proof.
intros ms₁ ms₂ H.
unfold eq_min_sl in H; unfold eq_min_sl.
destruct H as (H₁, (H₂, (H₃, H₄))).
split; [ symmetry; assumption | idtac ].
split; [ symmetry; assumption | idtac ].
split; symmetry; assumption.
Qed.

Theorem eq_ms_trans : transitive _ eq_min_sl.
Proof.
intros ms₁ ms₂ ms₃ H I.
unfold eq_min_sl in H, I; unfold eq_min_sl.
destruct H as (H₁, (H₂, (H₃, H₄))).
destruct I as (I₁, (I₂, (I₃, I₄))).
split; [ etransitivity; eassumption | idtac ].
split; [ etransitivity; eassumption | idtac ].
split; etransitivity; eassumption.
Qed.

Add Parametric Relation : min_sl eq_min_sl
 reflexivity proved by eq_ms_refl
 symmetry proved by eq_ms_sym
 transitivity proved by eq_ms_trans
 as eq_ms_rel.

Add Parametric Morphism : newton_segment_of_pair
  with signature eq_hs ==> eq_hs ==> eq_ns
  as newton_segment_of_pair_morph.
Proof.
intros hs₁ hs₂ Heq₁ hs₃ hs₄ Heq₃.
inversion_clear Heq₁.
inversion_clear Heq₃.
split; simpl.
 inversion_clear H.
 inversion_clear H1.
 rewrite H3, H4, H, H5; reflexivity.

 split.
  inversion_clear H.
  inversion_clear H1.
  rewrite H3, H4, H, H5; reflexivity.

  split; [ assumption | idtac ].
  split; assumption.
Qed.

Add Parametric Morphism : (list_map_pairs newton_segment_of_pair)
  with signature eq_list_hs ==> eq_list_ns
  as list_map_pairs_ns_of_pair_morph.
Proof.
intros hsl₁ hsl₂ Heq.
unfold eq_list_ns.
unfold eq_list_hs in Heq.
induction Heq; [ reflexivity | simpl ].
destruct l as [| a].
 destruct l' as [| b]; [ constructor | inversion Heq ].

 destruct l' as [| b]; [ inversion Heq | idtac ].
 constructor; [ idtac | assumption ].
 rewrite H.
 inversion Heq; subst.
 rewrite H3.
 reflexivity.
Qed.

Add Parametric Morphism : slope
  with signature eq_min_sl ==> Qeq
  as slope_morph.
Proof.
intros ms₁ ms₂ Heq.
unfold eq_min_sl in Heq.
destruct Heq as (Hsl, (Hend, (Hseg, Hrem))).
assumption.
Qed.

Add Parametric Morphism : end_pt
  with signature eq_min_sl ==> eq_pt
  as end_pt_morph.
Proof.
intros ms₁ ms₂ Heq.
unfold eq_min_sl in Heq.
destruct Heq as (Hsl, (Hend, (Hseg, Hrem))).
assumption.
Qed.

Add Parametric Morphism : seg
  with signature eq_min_sl ==> eq_list_pt
  as seg_morph.
Proof.
intros ms₁ ms₂ Heq.
unfold eq_min_sl in Heq.
destruct Heq as (Hsl, (Hend, (Hseg, Hrem))).
assumption.
Qed.

Add Parametric Morphism : rem_pts
  with signature eq_min_sl ==> eq_list_pt
  as rem_pts_morph.
Proof.
intros ms₁ ms₂ Heq.
unfold eq_min_sl in Heq.
destruct Heq as (Hsl, (Hend, (Hseg, Hrem))).
assumption.
Qed.

Add Parametric Morphism : slope_expr
  with signature eq_pt ==> eq_pt ==> Qeq
  as slope_expr_morph.
Proof.
intros pt₁ pt₂ Heq₁ pt₃ pt₄ Heq₃.
unfold slope_expr.
unfold eq_pt in Heq₁, Heq₃.
destruct Heq₁ as (H₁, H₂).
destruct Heq₃ as (H₃, H₄).
rewrite H₁, H₂, H₃, H₄; reflexivity.
Qed.

Add Parametric Morphism : minimise_slope
  with signature eq_pt ==> eq_pt ==> eq_list_pt ==> eq_min_sl
  as minimise_slope_morph.
Proof.
intros pt₁ pt₂ Heq₁ pt₃ pt₄ Heq₃ pts₁ pts₂ Hpts.
revert pt₁ pt₂ pt₃ pt₄ Heq₁ Heq₃.
induction Hpts as [| pt₅ pt₆ pts₅ pts₆]; intros; simpl.
 unfold eq_min_sl; simpl.
 unfold slope_expr.
 split.
  destruct Heq₁ as (Hfst₁, Hsnd₁).
  destruct Heq₃ as (Hfst₃, Hsnd₃).
  rewrite Hfst₁, Hsnd₁, Hfst₃, Hsnd₃.
  reflexivity.

  split; [ assumption | idtac ].
  split; reflexivity.

 pose proof (IHHpts pt₁ pt₂ pt₅ pt₆ Heq₁ H) as Heq.
 remember (minimise_slope pt₁ pt₅ pts₅) as ms₁.
 remember (minimise_slope pt₂ pt₆ pts₆) as ms₂.
 rewrite <- Heq.
 rewrite <- Heq₁, <- Heq₃.
 remember (slope_expr pt₁ pt₃ ?= slope ms₁) as c.
 symmetry in Heqc.
 destruct c.
  unfold eq_min_sl; simpl.
  split; [ rewrite Heq; reflexivity | idtac ].
  split; [ rewrite Heq; reflexivity | idtac ].
  split; [ idtac | rewrite Heq; reflexivity ].
  constructor; [ assumption | idtac ].
  rewrite Heq; reflexivity.

  unfold eq_min_sl; simpl.
  split; [ rewrite Heq₁, Heq₃; reflexivity | idtac ].
  split; [ assumption | idtac ].
  split; [ reflexivity | idtac ].
  constructor; [ assumption | assumption ].

  assumption.
Qed.

Add Parametric Morphism : lower_convex_hull_points
  with signature eq_list_pt ==> eq_list_hs
  as lower_convex_hull_points_morph.
Proof.
intros pts₁ pts₂ Heq.
unfold lower_convex_hull_points.
erewrite list_forall2_length; [ idtac | eassumption ].
remember (length pts₂) as len; clear Heqlen.
revert pts₁ pts₂ Heq.
induction len; intros; [ reflexivity | simpl ].
destruct pts₁ as [| pt₁]; simpl.
 destruct pts₂ as [| pt₂]; [ reflexivity | inversion Heq ].

 destruct pts₂ as [| pt₂]; [ inversion Heq | idtac ].
 inversion_clear Heq.
 destruct pts₁ as [| pt₃]; simpl.
  destruct pts₂ as [| pt₄]; [ simpl | inversion H0 ].
  constructor; [ idtac | reflexivity ].
  constructor; [ assumption | reflexivity ].

  destruct pts₂ as [| pt₄]; [ inversion H0 | simpl ].
  constructor.
   constructor; [ assumption | simpl ].
   inversion_clear H0.
   rewrite H, H1, H2; reflexivity.

   rewrite fold_eq_list_hs.
   apply IHlen.
   constructor.
    inversion_clear H0.
    rewrite H, H1, H2; reflexivity.

    inversion_clear H0.
    rewrite H, H1, H2; reflexivity.
Qed.

Add Parametric Morphism α (R : ring α) : (@newton_segments _ R)
  with signature @ps_pol_eq _ R ==> eq_list_ns
  as newton_segments_morph.
Proof.
intros Pa Pb HP.
unfold newton_segments.
rewrite HP; reflexivity.
Qed.

Add Parametric Morphism : (@List.hd newton_segment)
  with signature eq_ns ==> eq_list_ns ==> eq_ns
  as list_hd_ns_morph.
Proof.
intros nsa nsb Hab nsc nsd Hcd.
induction Hcd; assumption.
Qed.

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

Definition phony_ns :=
  {| γ := 0; β := 0; ini_pt := (0, 0); fin_pt := (0, 0); oth_pts := [] |}.

Lemma zzz : ∀ pol ns c₁ r pol₁ ns₁ j₁ αj₁ k₁ αk₁,
  ns ∈ newton_segments pol
  → c₁ = ac_root (Φq pol ns) ∧ (c₁ ≠ 0)%K
  → r = root_multiplicity acf c₁ (Φq pol ns)
  → pol₁ = next_pol pol (β ns) (γ ns) c₁
  → r = 1%nat
  → ns₁ = List.hd phony_ns (newton_segments pol₁)
  → ini_pt ns₁ = (Qnat j₁, αj₁)
  → fin_pt ns₁ = (Qnat k₁, αk₁)
  → j₁ = 0%nat ∧ k₁ = 1%nat ∧ αj₁ > 0 ∧ αk₁ = 0.
Proof.
intros pol ns c₁ r pol₁ ns₁ j₁ αj₁ k₁ αk₁.
intros Hns Hc₁ Hr Hpol₁ Hr₁1 Hns₁ Hini₁ Hfin₁.
remember (quotient_phi_x_sub_c_pow_r (Φq pol ns) c₁ r) as Ψ eqn:HΨ .
remember Hns as Hini; clear HeqHini.
apply exists_ini_pt_nat in Hini.
destruct Hini as (j, (αj, Hini)).
eapply f₁_eq_term_with_Ψ_plus_g in Hpol₁; try eassumption.
assert (ns₁ = ns₁)%ns as H by reflexivity.
rewrite Hns₁ in H at 2.
clear Hns₁; rename H into Hns₁.
rewrite Hpol₁ in Hns₁.
unfold newton_segments in Hns₁.
unfold points_of_ps_polynom in Hns₁.
simpl in Hns₁.
unfold points_of_ps_lap in Hns₁.
unfold points_of_ps_lap_gen in Hns₁.
unfold qpower_list in Hns₁.
bbb.

(*
Fixpoint root_loop α {R : ring α} {K : field R} {acf : algeb_closed_field K}
    (pol : polynomial (puiseux_series α)) ns c₁ γ_sum :=
  let f₁ := pol₁ pol (β ns) (γ ns) c₁ in
  match newton_segments f₁ with
  | [] => 0%ps
  | [ns₁ … _] =>
      let c₂ := ac_root (Φq f₁ ns₁) in
      let t₂ := ps_monom c₂ (γ_sum + γ ns₁) in
      (t₂ + root_loop pol ns c₂ (γ_sum + γ ns₁)%Q)%ps
  end.

Definition root α {R : ring α} {K : field R} {acf : algeb_closed_field K}
    (pol : polynomial (puiseux_series α)) :=
  match newton_segments pol with
  | [] => 0%ps
  | [ns … _] =>
      let c₁ := ac_root (Φq pol ns) in
      let t₁ := ps_monom c₁ (γ ns) in
      (t₁ + root_loop pol ns c₁ (γ ns))%ps
  end.
*)
