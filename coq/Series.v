(* $Id: Series.v,v 1.55 2013-08-21 04:28:16 deraugla Exp $ *)

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

Section field.
 
Variable α : Type.
Variable fld : field α.
Notation "a ≍ b" := (fld_eq fld a b) (at level 70).

Definition series_0 := {| terms i := zero fld; stop := ∞ |}.

Inductive eq_series : series α → series α → Prop :=
  eq_series_base : ∀ s₁ s₂,
    (∀ i, fld_eq fld (series_nth_fld fld i s₁) (series_nth_fld fld i s₂))
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
(* simplifiable peut-être en réordonnant les conditions *)
(* cf Add Parametric Relation α (fld : field α) : (series α) (eq_series fld)
   ci-dessous : s'en inspirer *)
intros s₁ s₂ s₃.
unfold series_add; simpl.
constructor; simpl.
intros i.
unfold series_nth_fld; simpl.
rewrite Nbar.max_assoc.
remember (Nbar.max (Nbar.max (stop s₁) (stop s₂)) (stop s₃)) as n.
destruct (Nbar.lt_dec (fin i) n) as [Hlt₁| ]; [ subst n | reflexivity ].
destruct (Nbar.lt_dec (fin i) (Nbar.max (stop s₁) (stop s₂))) as [Hlt₂| Hge₂].
 destruct (Nbar.lt_dec (fin i) (stop s₁)) as [Hlt₃| Hge₃].
  destruct (Nbar.lt_dec (fin i) (stop s₂)) as [Hlt₄| Hge₄].
   destruct (Nbar.lt_dec (fin i) (stop s₃)) as [Hlt₅| Hge₅].
    destruct (Nbar.lt_dec (fin i) (Nbar.max (stop s₂) (stop s₃))).
     apply fld_add_assoc.

     exfalso; apply n; clear n.
     apply Nbar.max_lt_iff; left; assumption.

    destruct (Nbar.lt_dec (fin i) (Nbar.max (stop s₂) (stop s₃))).
     apply fld_add_assoc.

     exfalso; apply n; clear n.
     apply Nbar.max_lt_iff; left; assumption.

   destruct (Nbar.lt_dec (fin i) (stop s₃)) as [Hlt₅| Hge₅].
    destruct (Nbar.lt_dec (fin i) (Nbar.max (stop s₂) (stop s₃))).
     apply fld_add_assoc.

     exfalso; apply n; clear n.
     apply Nbar.max_lt_iff; right; assumption.

    destruct (Nbar.lt_dec (fin i) (Nbar.max (stop s₂) (stop s₃))).
     apply fld_add_assoc.

     rewrite fld_add_comm, fld_add_neutral; reflexivity.

  destruct (Nbar.lt_dec (fin i) (stop s₂)) as [Hlt₄| Hge₄].
   destruct (Nbar.lt_dec (fin i) (stop s₃)) as [Hlt₅| Hge₅].
    destruct (Nbar.lt_dec (fin i) (Nbar.max (stop s₂) (stop s₃))).
     apply fld_add_assoc.

     exfalso; apply n; clear n.
     apply Nbar.max_lt_iff; left; assumption.

    destruct (Nbar.lt_dec (fin i) (Nbar.max (stop s₂) (stop s₃))).
     apply fld_add_assoc.

     exfalso; apply n; clear n.
     apply Nbar.max_lt_iff; left; assumption.

   destruct (Nbar.lt_dec (fin i) (stop s₃)) as [Hlt₅| Hge₅].
    destruct (Nbar.lt_dec (fin i) (Nbar.max (stop s₂) (stop s₃))).
     apply fld_add_assoc.

     exfalso; apply n; clear n.
     apply Nbar.max_lt_iff; right; assumption.

    destruct (Nbar.lt_dec (fin i) (Nbar.max (stop s₂) (stop s₃))).
     apply fld_add_assoc.

     rewrite fld_add_comm, fld_add_neutral; reflexivity.

 destruct (Nbar.lt_dec (fin i) (stop s₃)) as [Hlt₅| Hge₅].
  destruct (Nbar.lt_dec (fin i) (stop s₁)) as [Hlt₃| Hge₃].
   destruct (Nbar.lt_dec (fin i) (Nbar.max (stop s₂) (stop s₃))).
    destruct (Nbar.lt_dec (fin i) (stop s₂)) as [Hlt₄| Hge₄].
     exfalso; apply Hge₂; clear Hge₂.
     apply Nbar.max_lt_iff; left; assumption.

     exfalso; apply Hge₂; clear Hge₂.
     apply Nbar.max_lt_iff; left; assumption.

    exfalso; apply Hge₂; clear Hge₂.
    apply Nbar.max_lt_iff; left; assumption.

   destruct (Nbar.lt_dec (fin i) (Nbar.max (stop s₂) (stop s₃))).
    destruct (Nbar.lt_dec (fin i) (stop s₂)) as [Hlt₄| Hge₄].
     exfalso; apply Hge₂; clear Hge₂.
     apply Nbar.max_lt_iff; right; assumption.

     do 2 rewrite fld_add_neutral; reflexivity.

    exfalso; apply n; clear n.
    apply Nbar.max_lt_iff; right; assumption.

  destruct (Nbar.lt_dec (fin i) (stop s₁)) as [Hlt₃| Hge₃].
   destruct (Nbar.lt_dec (fin i) (Nbar.max (stop s₂) (stop s₃))).
    destruct (Nbar.lt_dec (fin i) (stop s₂)) as [Hlt₄| Hge₄].
     exfalso; apply Hge₂; clear Hge₂.
     apply Nbar.max_lt_iff; left; assumption.

     exfalso; apply Hge₂; clear Hge₂.
     apply Nbar.max_lt_iff; left; assumption.

    exfalso; apply Hge₂; clear Hge₂.
    apply Nbar.max_lt_iff; left; assumption.

   destruct (Nbar.lt_dec (fin i) (Nbar.max (stop s₂) (stop s₃))).
    destruct (Nbar.lt_dec (fin i) (stop s₂)) as [Hlt₄| Hge₄].
     exfalso; apply Hge₂; clear Hge₂.
     apply Nbar.max_lt_iff; right; assumption.

     do 2 rewrite fld_add_neutral; reflexivity.

    reflexivity.
Qed.

End field.

Notation "a ≍ b" := (fld_eq _ a b) (at level 70).

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

   rewrite fld_add_neutral; reflexivity.

 destruct lt₁ as [Hlt₁| Hge₁].
  exfalso; apply Hge₅; clear Hge₅.
  apply Nbar.max_lt_iff; left; assumption.

  destruct lt₃ as [Hlt₃| Hge₃].
   exfalso; apply Hge₅; clear Hge₅.
   apply Nbar.max_lt_iff; right; assumption.

   destruct lt₆ as [Hlt₆| Hge₆]; [ idtac | reflexivity ].
   rewrite <- Hi₁, <- Hi₂.
   rewrite fld_add_neutral; reflexivity.
Qed.
