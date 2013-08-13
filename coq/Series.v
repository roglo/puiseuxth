(* $Id: Series.v,v 1.35 2013-08-13 18:37:38 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Field.

Set Implicit Arguments.

Record series α :=
  { terms : nat → α;
    stop : option nat }.

Definition series_nth α n (s : series α) :=
  match stop s with
  | Some st => if lt_dec n st then Some (terms s n) else None
  | None => None
  end.

Section field.
 
Variable α : Type.
Variable fld : field α.

Definition series_0 := {| terms i := zero fld; stop := Some 0%nat |}.

Inductive eq_series : series α → series α → Prop :=
  eq_series_base : ∀ s₁ s₂,
    (∀ i, fld_eq fld (terms s₁ i) (terms s₂ i))
    → stop s₁ = stop s₂
      → eq_series s₁ s₂.

Notation "a ≃ b" := (eq_series a b) (at level 70).

Theorem eq_series_refl : reflexive _ eq_series.
Proof.
intros s.
constructor; [ idtac | reflexivity ].
intros; reflexivity.
Qed.

Theorem eq_series_sym : symmetric _ eq_series.
Proof.
intros s₁ s₂ H.
inversion H; subst.
constructor; [ idtac | symmetry; assumption ].
intros i.
symmetry.
apply H0.
Qed.

Theorem eq_series_trans : transitive _ eq_series.
Proof.
intros s₁ s₂ s₃ H₁ H₂.
inversion H₁; inversion H₂; subst.
constructor.
 intros.
 etransitivity; [ apply H | apply H3 ].

 transitivity (stop s₂); assumption.
Qed.

Definition series_add s₁ s₂ :=
  {| terms i := add fld (terms s₁ i) (terms s₂ i);
     stop :=
       match stop s₁ with
       | Some st₁ =>
           match stop s₂ with
           | Some st₂ => Some (max st₁ st₂)
           | None => None
           end
       | None => None
       end |}.

Lemma series_add_comm : ∀ s₁ s₂,
  series_add s₁ s₂ ≃ series_add s₂ s₁.
Proof.
intros s₁ s₂.
constructor; simpl.
 intros i.
 apply fld_add_comm.

 destruct (stop s₁), (stop s₂); try reflexivity.
 rewrite Nat.max_comm; reflexivity.
Qed.

Lemma series_add_assoc : ∀ s₁ s₂ s₃,
  series_add (series_add s₁ s₂) s₃ ≃ series_add s₁ (series_add s₂ s₃).
Proof.
intros s₁ s₂ s₃.
unfold series_add; simpl.
constructor; simpl.
 intros i.
 apply fld_add_assoc.

 destruct (stop s₁) as [a| ]; [ idtac | reflexivity ].
 destruct (stop s₂) as [b| ]; [ idtac | reflexivity ].
 destruct (stop s₃) as [c| ]; [ idtac | reflexivity ].
 f_equal.
 symmetry.
 apply Nat.max_assoc.
Qed.

End field.

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
 rewrite H, H1; reflexivity.

 rewrite H0, H2; reflexivity.
Qed.
