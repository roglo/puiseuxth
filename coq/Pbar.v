(* $Id: Pbar.v,v 1.1 2013-08-24 22:09:23 deraugla Exp $ *)

Require Import Utf8.
Require Import ZArith.

Set Implicit Arguments.

Inductive Pbar : Set :=
  | pfin : ∀ x : positive, Pbar
  | pinf : Pbar.

Delimit Scope Nbar_scope with Pbar.
Bind Scope Nbar_scope with Pbar.

Notation "∞" := pinf.
Notation "1" := (pfin xH) : Pbar_scope.

Open Scope Pbar_scope.

Module Pbar.

Definition to_nat pb :=
  match pb with
  | pfin n => Pos.to_nat n
  | ∞ => O
  end.

End Pbar.

Close Scope Pbar_scope.
