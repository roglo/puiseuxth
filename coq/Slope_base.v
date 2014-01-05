(* Slope_base.v *)

Require Import Utf8.
Require Import QArith.

Definition slope_expr pt₁ pt₂ :=
  Qdiv (Qminus (snd pt₂) (snd pt₁)) (Qminus (fst pt₂) (fst pt₁)).

Lemma fold_slope_expr : ∀ x₁ y₁ x₂ y₂,
  (y₂ - y₁) / (x₂ - x₁) = slope_expr (x₁, y₁) (x₂, y₂).
Proof. reflexivity. Qed.
