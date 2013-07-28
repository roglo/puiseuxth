(* $Id: Series.v,v 1.29 2013-07-28 10:32:26 deraugla Exp $ *)

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

Inductive eq_series α fld : series α → series α → Prop :=
  eq_ser' : ∀ s₁ s₂,
    (∀ i, fld_eq fld (terms s₁ i) (terms s₂ i))
    → stop s₁ = stop s₂
      → eq_series fld s₁ s₂.

Theorem eq_series_refl : ∀ α (fld : field α), reflexive _ (eq_series fld).
Proof.
intros α fld s.
constructor; [ idtac | reflexivity ].
intros; reflexivity.
Qed.

Theorem eq_series_sym : ∀ α (fld : field α), symmetric _ (eq_series fld).
Proof.
intros α fld s₁ s₂ H.
inversion H; subst.
constructor; [ idtac | symmetry; assumption ].
intros i.
symmetry.
apply H0.
Qed.

Theorem eq_series_trans : ∀ α (fld : field α), transitive _ (eq_series fld).
Proof.
intros α fld s₁ s₂ s₃ H₁ H₂.
inversion H₁; inversion H₂; subst.
constructor.
 intros.
 etransitivity; [ apply H | apply H3 ].

 transitivity (stop s₂); assumption.
Qed.

Add Parametric Relation α (fld : field α) : (series α) (eq_series fld)
 reflexivity proved by (eq_series_refl fld)
 symmetry proved by (eq_series_sym (fld := fld))
 transitivity proved by (eq_series_trans (fld := fld))
 as eq_series_rel.

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
