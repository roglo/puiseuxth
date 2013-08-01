(* $Id: Series.v,v 1.32 2013-08-01 19:25:59 deraugla Exp $ *)

Require Import Utf8.
Require Import QArith.
Require Import NPeano.

Require Import Field.

Set Implicit Arguments.

Record series α := mkser
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

Definition stretch_series k s :=
  {| terms i :=
       if zerop (i mod k) then terms s (i / k) else zero fld;
     stop :=
       match stop s with
       | Some st => Some (st * k)%nat
       | None => None
       end |}.

Inductive eq_series : series α → series α → Prop :=
  | eq_series_stretch_l_inf : ∀ k t₁ t₂,
      (∀ i, fld_eq fld (t₁ (Pos.to_nat k * i)%nat) (t₂ i))
      → eq_series (mkser t₁ None) (mkser t₂ None)
  | eq_series_stretch_l_fin : ∀ k t₁ t₂ st₁ st₂,
      (∀ i, fld_eq fld (t₁ (Pos.to_nat k * i)%nat) (t₂ i))
      → st₂ = (Pos.to_nat k * st₁)%nat
        → eq_series (mkser t₁ (Some st₁)) (mkser t₂ (Some st₂))
  | eq_series_symmetry : ∀ s₁ s₂,
      eq_series s₁ s₂ → eq_series s₂ s₁.

Notation "a ≃ b" := (eq_series fld a b)  (at level 70).

Theorem eq_series_refl : reflexive _ eq_series.
Proof.
intros s.
destruct s as (t, [s| ]); simpl.
 constructor 2 with (k := 1%positive).
  intros; rewrite mult_1_l; reflexivity.

  rewrite mult_1_l; reflexivity.

 constructor 1 with (k := 1%positive).
 intros; rewrite mult_1_l; reflexivity.
Qed.

Theorem eq_series_sym : symmetric _ eq_series.
Proof.
intros s₁ s₂ H.
constructor; assumption.
Qed.

Theorem eq_series_trans : transitive _ eq_series.
Proof.
intros s₁ s₂ s₃ H₁ H₂.
inversion H₁ as [k₁ t₁ t₂| k₁ t₁ t₂| ]; subst.
 inversion H₂ as [k₂ t₃ t₄| k₂ t₃ t₄| ]; subst.
  constructor 1 with (k := (k₁ * k₂)%positive).
  intros i.
  rewrite Pos2Nat.inj_mul.
  rewrite <- mult_assoc.
  etransitivity; [ apply H | apply H1 ].
bbb.

Definition series_add α (fld : field α) s₁ s₂ :=
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

Lemma series_add_comm : ∀ α (fld : field α) s₁ s₂,
  eq_series fld (series_add fld s₁ s₂) (series_add fld s₂ s₁).
Proof.
intros α fld s₁ s₂.
constructor; simpl.
 intros i.
 apply fld_add_comm.

 destruct (stop s₁), (stop s₂); try reflexivity.
 rewrite Nat.max_comm; reflexivity.
Qed.

Lemma series_add_assoc : ∀ α (fld : field α) s₁ s₂ s₃,
  eq_series fld
    (series_add fld (series_add fld s₁ s₂) s₃)
    (series_add fld s₁ (series_add fld s₂ s₃)).
Proof.
intros α fld s₁ s₂ s₃.
unfold series_add.
simpl.
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

Add Parametric Relation α (fld : field α) : (series α) (eq_series fld)
 reflexivity proved by (eq_series_refl fld)
 symmetry proved by (eq_series_sym (fld := fld))
 transitivity proved by (eq_series_trans (fld := fld))
 as eq_series_rel.

Add Parametric Morphism α (fld : field α) : (@series_add α fld) with 
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
