(* $Id: Series.v,v 1.44 2013-08-20 06:14:12 deraugla Exp $ *)

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
  | nfin st => if lt_dec n st then Some (terms s n) else None
  | ∞ => Some (terms s n)
  end.

Definition series_nth_fld α fld n (s : series α) :=
  if Nbar.lt_dec (nfin n) (stop s) then terms s n else zero fld.

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
  {| terms i := add fld (terms s₁ i) (terms s₂ i);
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
 destruct (Nbar.lt_dec (nfin i) (nfin n)) as [Hlt| ]; [ idtac | reflexivity ].
 rewrite fld_add_comm; reflexivity.

 destruct (Nbar.lt_dec (nfin i) ∞); [ idtac | reflexivity ].
 apply fld_add_comm.
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
remember (Nbar.max (Nbar.max (stop s₁) (stop s₂)) (stop s₃)) as n.
symmetry in Heqn.
destruct n as [n| ].
 destruct (lt_dec i n) as [Hlt| Hge]; [ idtac | reflexivity ].
 rewrite fld_add_assoc; reflexivity.

 rewrite fld_add_assoc; reflexivity.
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
destruct (Nbar.lt_dec (stop s₁) (stop s₃)) as [Hlt₁| Hge₁].
 rewrite Nbar.max_r; [ idtac | apply Nbar.lt_le_incl; assumption ].
 Focus 1.
 destruct (stop s₃) as [st₃| ].
  destruct (lt_dec i st₃) as [Hlt₂| Hgt₂].
   destruct (Nbar.lt_dec (stop s₂) (stop s₄)) as [Hlt₃| Hge₃].
    Focus 1.
    rewrite Nbar.max_r; [ idtac | apply Nbar.lt_le_incl; assumption ].
    destruct (stop s₄) as [st₄| ].
     destruct (lt_dec i st₄) as [Hlt₄| Hgte₄].

bbb.

intros s₁ s₂ Heq₁ s₃ s₄ Heq₂.
inversion Heq₁; subst.
inversion Heq₂; subst.
constructor; simpl.
 intros i.
 rewrite H, H1; reflexivity.

 rewrite H0, H2; reflexivity.
Qed.
