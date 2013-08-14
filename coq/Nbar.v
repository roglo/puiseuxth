(* $Id: Nbar.v,v 1.1 2013-08-14 12:14:29 deraugla Exp $ *)

Require Import Utf8.
Require Import Arith.

Set Implicit Arguments.

Inductive Nbar : Set :=
  | nfin : ∀ x : nat, Nbar
  | ninf : Nbar.

Notation "∞" := ninf.

Delimit Scope Nbar_scope with Nbar.
Bind Scope Nbar_scope with Nbar.

Notation "0" := (nfin 0) : Nbar_scope.

Open Scope Nbar_scope.

Close Scope Nbar_scope.
