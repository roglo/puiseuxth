(* Slope_base.v *)

From Stdlib Require Import Utf8.
Require Import QG.
Open Scope QG.

Definition slope_expr pt₁ pt₂ :=
  (snd pt₂ - snd pt₁) / (fst pt₂ - fst pt₁).
