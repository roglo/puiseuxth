(* Slope_base.v *)

From Stdlib Require Import Utf8.
Require Import QGArith.
Open Scope QG.

Definition slope_expr pt₁ pt₂ :=
  (snd pt₂ - snd pt₁) / (QG_of_nat (fst pt₂) - QG_of_nat (fst pt₁)).
