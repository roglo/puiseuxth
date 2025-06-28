(* Slope_base.v *)

From Stdlib Require Import Utf8.
Require Import A_Pos A_ZArith A_QArith.

Definition slope_expr pt₁ pt₂ :=
  ((snd pt₂ - snd pt₁) /
     ((Z.of_nat (fst pt₂) # 1) - (Z.of_nat (fst pt₁) # 1)))%Q.
