(* Slope_base.v *)

Require Import Utf8.
Require Import QArith.

Definition slope_expr pt₁ pt₂ :=
  (snd pt₂ - snd pt₁) / (fst pt₂ - fst pt₁).
