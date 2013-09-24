(* $Id: Series.v,v 1.65 2013-09-24 01:12:02 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Field.
Require Import Nbar.

Set Implicit Arguments.

Record series α :=
  { terms : nat → α;
    stop : Nbar }.

Definition series_nth α n (s : series α) :=
  match stop s with
  | fin st => if lt_dec n st then Some (terms s n) else None
  | ∞ => Some (terms s n)
  end.

Definition series_nth_fld α fld n (s : series α) :=
  if Nbar.lt_dec (fin n) (stop s) then terms s n else zero fld.

Theorem stop_0_series_nth_None : ∀ α (s : series α),
  stop s = 0%Nbar → series_nth 0 s = None.
Proof.
intros α s Hs.
unfold series_nth.
rewrite Hs; reflexivity.
Qed.

Section field.
 
Variable α : Type.
Variable fld : field α.
Notation "a ≍ b" := (fld_eq fld a b) (at level 70).

Definition series_0 := {| terms i := zero fld; stop := fin 0 |}.

Inductive eq_series : series α → series α → Prop :=
  eq_series_base : ∀ s₁ s₂,
    (∀ i, series_nth_fld fld i s₁ ≍ series_nth_fld fld i s₂)
    → eq_series s₁ s₂.

Notation "a ≃ b" := (eq_series a b) (at level 70).

Theorem eq_series_refl : reflexive _ eq_series.
Proof.
intros s.
constructor; reflexivity.
Qed.

Theorem eq_series_sym : symmetric _ eq_series.
Proof.
intros s₁ s₂ H.
inversion H; subst.
constructor.
intros i; symmetry; apply H0.
Qed.

Theorem eq_series_trans : transitive _ eq_series.
Proof.
intros s₁ s₂ s₃ H₁ H₂.
inversion H₁; inversion H₂; subst.
constructor.
etransitivity; [ apply H | apply H2 ].
Qed.

Definition series_add s₁ s₂ :=
  {| terms i := add fld (series_nth_fld fld i s₁) (series_nth_fld fld i s₂);
     stop := Nbar.max (stop s₁) (stop s₂) |}.

Definition series_neg s :=
  {| terms i := neg fld (terms s i); stop := stop s |}.

Lemma series_add_comm : ∀ s₁ s₂,
  series_add s₁ s₂ ≃ series_add s₂ s₁.
Proof.
intros s₁ s₂.
constructor; simpl.
intros i.
unfold series_nth_fld; simpl.
rewrite Nbar.max_comm.
destruct (Nbar.max (stop s₂) (stop s₁)) as [n| ].
 destruct (Nbar.lt_dec (fin i) (fin n)) as [Hlt| ]; [ idtac | reflexivity ].
 rewrite fld_add_comm; reflexivity.

 destruct (Nbar.lt_dec (fin i) ∞); [ idtac | reflexivity ].
 rewrite fld_add_comm; reflexivity.
Qed.

Lemma series_add_assoc : ∀ s₁ s₂ s₃,
  series_add (series_add s₁ s₂) s₃ ≃ series_add s₁ (series_add s₂ s₃).
Proof.
intros s₁ s₂ s₃.
unfold series_add; simpl.
constructor; simpl.
intros i.
unfold series_nth_fld; simpl.
rewrite Nbar.max_assoc.
remember (Nbar.lt_dec (fin i) (stop s₁)) as lt₁.
remember (Nbar.lt_dec (fin i) (stop s₂)) as lt₂.
remember (Nbar.lt_dec (fin i) (stop s₃)) as lt₃.
remember (Nbar.lt_dec (fin i) (Nbar.max (stop s₁) (stop s₂))) as lt₄.
remember (Nbar.lt_dec (fin i) (Nbar.max (stop s₂) (stop s₃))) as lt₅.
clear Heqlt₁ Heqlt₂ Heqlt₃ Heqlt₄ Heqlt₅.
remember (Nbar.max (Nbar.max (stop s₁) (stop s₂)) (stop s₃)) as n.
destruct (Nbar.lt_dec (fin i) n) as [Hlt| ]; [ subst n | reflexivity ].
destruct lt₄ as [Hlt₄| Hge₄].
 destruct lt₅ as [Hlt₅| Hge₅].
  destruct lt₁ as [Hlt₁| Hge₁].
   destruct lt₂ as [Hlt₂| Hge₂].
    destruct lt₃ as [Hlt₃| Hge₃]; [ apply fld_add_assoc | idtac ].
    rewrite fld_add_comm, fld_add_0_l; symmetry.
    rewrite <- fld_add_assoc.
    rewrite fld_add_comm, fld_add_0_l; reflexivity.

    rewrite fld_add_assoc, fld_add_0_l; reflexivity.

   rewrite fld_add_assoc, fld_add_0_l; reflexivity.

  symmetry.
  rewrite fld_add_comm, fld_add_0_l; symmetry.
  destruct lt₂ as [Hlt₂| Hge₂].
   exfalso; apply Hge₅; clear Hge₅.
   apply Nbar.max_lt_iff; left; assumption.

   rewrite fld_add_assoc, fld_add_0_l.
   destruct lt₃ as [Hlt₃| Hge₃].
    exfalso; apply Hge₅; clear Hge₅.
    apply Nbar.max_lt_iff; right; assumption.

    rewrite fld_add_comm, fld_add_0_l; reflexivity.

 rewrite fld_add_0_l.
 destruct lt₁ as [Hlt₁| Hge₁].
  exfalso; apply Hge₄; clear Hge₄.
  apply Nbar.max_lt_iff; left; assumption.

  rewrite fld_add_0_l.
  destruct lt₂ as [Hlt₂| Hge₂].
   exfalso; apply Hge₄; clear Hge₄.
   apply Nbar.max_lt_iff; right; assumption.

   destruct lt₅ as [Hlt₅| Hge₅].
    rewrite fld_add_0_l; reflexivity.

    destruct lt₃ as [Hlt₃| Hge₃]; [ idtac | reflexivity ].
    exfalso; apply Hge₅; clear Hge₅.
    apply Nbar.max_lt_iff; right; assumption.
Qed.

Lemma stop_series_add_0_l : ∀ s, stop (series_add series_0 s) = stop s.
Proof.
intros s; simpl.
destruct (stop s); reflexivity.
Qed.

Lemma series_nth_series_0 : ∀ i, series_nth_fld fld i series_0 ≍ zero fld.
Proof.
intros i.
unfold series_nth_fld; simpl.
destruct (Nbar.lt_dec (fin i) 0); reflexivity.
Qed.

Lemma series_add_0_l : ∀ s, series_add series_0 s ≃ s.
Proof.
intros s.
constructor; intros i.
unfold series_nth_fld.
rewrite stop_series_add_0_l; simpl.
remember (Nbar.lt_dec (fin i) (stop s)) as d.
destruct d as [H₁| H₁]; [ idtac | reflexivity ].
rewrite series_nth_series_0.
rewrite fld_add_0_l.
unfold series_nth_fld.
rewrite <- Heqd; reflexivity.
Qed.

Lemma series_add_neg : ∀ s, series_add s (series_neg s) ≃ series_0.
Proof.
intros s.
constructor; intros i.
unfold series_nth_fld; simpl.
rewrite Nbar.max_id.
destruct (Nbar.lt_dec (fin i) 0) as [H₁| H₁].
 exfalso; revert H₁; apply Nbar.nlt_0_r.

 clear H₁.
 unfold series_nth_fld; simpl.
 destruct (Nbar.lt_dec (fin i) (stop s)) as [H₁| H₁]; [ idtac | reflexivity ].
 apply fld_add_neg.
Qed.

End field.

Notation "a ≍ b" := (fld_eq _ a b) (at level 70).
Notation "a ≭ b" := (not (fld_eq _ a b)) (at level 70).

Add Parametric Relation α (fld : field α) : (series α) (eq_series fld)
 reflexivity proved by (eq_series_refl fld)
 symmetry proved by (eq_series_sym (fld := fld))
 transitivity proved by (eq_series_trans (fld := fld))
 as eq_series_rel.

Add Parametric Morphism α (fld : field α) : (series_add fld) with 
signature eq_series fld ==> eq_series fld ==> eq_series fld
as series_add_morph.
Proof.
intros s₁ s₂ Heq₁ s₃ s₄ Heq₂.
inversion Heq₁; subst.
inversion Heq₂; subst.
constructor; simpl.
intros i.
unfold series_nth_fld; simpl.
unfold series_nth_fld in H; simpl in H.
unfold series_nth_fld in H0; simpl in H0.
pose proof (H i) as Hi₁.
pose proof (H0 i) as Hi₂.
clear H H0.
unfold series_nth_fld.
remember (Nbar.lt_dec (fin i) (stop s₁)) as lt₁.
remember (Nbar.lt_dec (fin i) (stop s₂)) as lt₂.
remember (Nbar.lt_dec (fin i) (stop s₃)) as lt₃.
remember (Nbar.lt_dec (fin i) (stop s₄)) as lt₄.
remember (Nbar.lt_dec (fin i) (Nbar.max (stop s₁) (stop s₃))) as lt₅.
remember (Nbar.lt_dec (fin i) (Nbar.max (stop s₂) (stop s₄))) as lt₆.
clear Heqlt₁ Heqlt₂ Heqlt₃ Heqlt₄ Heqlt₅ Heqlt₆.
move Hi₁ at bottom.
move Hi₂ at bottom.
destruct lt₅ as [Hlt₅| Hge₅].
 rewrite Hi₁, Hi₂.
 destruct lt₆ as [Hlt₆| Hge₆]; [ reflexivity | idtac ].
 destruct lt₂ as [Hlt₂| Hge₂].
  exfalso; apply Hge₆; clear Hge₆.
  apply Nbar.max_lt_iff; left; assumption.

  destruct lt₄ as [Hlt₄| Hge₄].
   exfalso; apply Hge₆; clear Hge₆.
   apply Nbar.max_lt_iff; right; assumption.

   rewrite fld_add_0_l; reflexivity.

 destruct lt₁ as [Hlt₁| Hge₁].
  exfalso; apply Hge₅; clear Hge₅.
  apply Nbar.max_lt_iff; left; assumption.

  destruct lt₃ as [Hlt₃| Hge₃].
   exfalso; apply Hge₅; clear Hge₅.
   apply Nbar.max_lt_iff; right; assumption.

   destruct lt₆ as [Hlt₆| Hge₆]; [ idtac | reflexivity ].
   rewrite <- Hi₁, <- Hi₂.
   rewrite fld_add_0_l; reflexivity.
Qed.

Add Parametric Morphism α (fld : field α) i : (series_nth_fld fld i) with 
signature (eq_series fld) ==> (fld_eq fld) as series_nth_fld_morph.
Proof.
intros s₁ s₂ Heq.
inversion Heq; subst.
apply H.
Qed.
