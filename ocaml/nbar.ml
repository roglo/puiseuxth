(* $Id: nbar.ml,v 1.1 2013-10-11 12:27:21 deraugla Exp $ *)

#load "./pa_coq.cmo";

Inductive Nbar : Set :=
  | fin : ∀ x : nat, Nbar
  | inf : Nbar.

value lt_dec n m =
  match n with
  | fin n →
      match m with
      | fin m → n ≤ n
      | inf → True
      end
  | inf → False
  end
;

