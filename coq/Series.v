(* $Id: Series.v,v 1.13 2013-07-24 07:25:56 deraugla Exp $ *)

Require Import Utf8.
Require Import Arith.

Set Implicit Arguments.

Record series α :=
  { term : nat → α;
    stop : option nat }.

Definition series_nth_opt α (n : nat) (s : series α) : option α :=
  match stop s with
  | Some i => if le_dec n i then None else Some (term s n)
  | None => Some (term s n)
  end.

Definition series_eq α elem_eq (s₁ s₂ : series α) :=
  (∀ i, elem_eq (term s₁ i) (term s₂ i) = true) ∧ stop s₁ = stop s₂.
