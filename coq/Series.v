(* $Id: Series.v,v 1.14 2013-07-24 12:17:55 deraugla Exp $ *)

Require Import Utf8.
Require Import Arith.

Require Import Field.

Set Implicit Arguments.

Record series α :=
  { term : nat → α;
    stop : option nat }.

Definition series_nth_opt α (n : nat) (s : series α) : option α :=
  match stop s with
  | Some i => if le_dec n i then None else Some (term s n)
  | None => Some (term s n)
  end.

Definition series_eq α fld (s₁ s₂ : series α) :=
  (∀ i, fld_eq fld (term s₁ i) (term s₂ i) = true) ∧ stop s₁ = stop s₂.

Lemma series_eq_refl : ∀ α fld (s : series α), series_eq fld s s.
Proof.
intros α fld s.
unfold series_eq; split; [ idtac | reflexivity ].
intros i; apply fld_eq_refl.
Qed.
