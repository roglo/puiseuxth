(* Puiseux.v *)

Require Import Utf8.
Require Import QArith.

Require Import Misc.
Require Import Qbar.
Require Import Field.
Require Import Fpolynomial.
Require Import Newton.
Require Import ConvexHull.
Require Import Puiseux_series.
Require Import Ps_add.
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

Delimit Scope list_pt_scope with pts.
Notation "a = b" := (eq_list_pt a b) : list_pt_scope.

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

Add Parametric Morphism α (R : ring α) : (@points_of_ps_polynom _ R)
  with signature @ps_pol_eq _ R ==> eq_list_pt
  as points_of_ps_polynom_morph.
Proof.
intros Pa Pb HP.
unfold points_of_ps_polynom.
inversion HP; subst.
 reflexivity.

 unfold points_of_ps_lap; simpl.
 unfold points_of_ps_lap_gen; simpl.
 simpl in H1.
 apply order_morph in H1.
 remember (order x₁) as o₁ eqn:Ho₁ .
 remember (order x₂) as o₂ eqn:Ho₂ .
 symmetry in Ho₁, Ho₂.
 destruct o₁ as [v₁| ].
  destruct o₂ as [v₂| ].
   apply Qbar.qfin_inj in H1.
   constructor; [ rewrite H1; reflexivity | idtac ].
   Focus 1.
bbb.

Add Parametric Morphism α (R : ring α) : (@newton_segments _ R)
  with signature @ps_pol_eq _ R ==> eq_list_pt
  as newton_segments_morph.
Proof.
intros Pa Pb HP.
unfold newton_segments.
bbb.

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
  → j₁ = 0%nat ∧ k₁ = 1%nat.
Proof.
intros pol ns c₁ r pol₁ ns₁ j₁ αj₁ k₁ αk₁.
intros Hns Hc₁ Hr Hpol₁ Hr₁1 Hns₁ Hini₁ Hfin₁.
remember (quotient_phi_x_sub_c_pow_r (Φq pol ns) c₁ r) as Ψ eqn:HΨ .
remember Hns as Hini; clear HeqHini.
apply exists_ini_pt_nat in Hini.
destruct Hini as (j, (αj, Hini)).
eapply f₁_eq_term_with_Ψ_plus_g in Hpol₁; try eassumption.
bbb.
rewrite Hpol₁ in Hns₁.

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
