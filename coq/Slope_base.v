(* Slope_base.v *)

From Stdlib Require Import Utf8 ZArith.

Definition slope_expr pt₁ pt₂ den :=
  ((snd pt₂ - snd pt₁)%Z,
   (den * Pos.of_nat (fst pt₂ - fst pt₁))%positive).
