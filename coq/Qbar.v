(* Qbar.v *)

Require Import Utf8.
Require Import QArith.

Set Implicit Arguments.

Inductive Qbar : Set :=
  | qfin : ∀ x : Q, Qbar
  | qinf : Qbar.

Delimit Scope Qbar_scope with Qbar.
Notation "∞" := qfin : Qbar_scope.
