(* $Id: puiseux_series.mli,v 1.1 2013-04-06 09:07:58 deraugla Exp $ *)

type monomial₂ α = { coeff₂ : α; power₂ : Pnums.Q.t };
type puiseux_series α = { monoms₂ : list (monomial₂ α) };

value pol_add₂ :
  (α → α → α) → (α → bool)
  → puiseux_series α → puiseux_series α → puiseux_series α;
(** [pol_add₂ add_coeff is_null_coeff p₁ p₂] *)

value pol_mul₂ :
  (α → α → α) → (α → α → α) → (α → bool)
  → puiseux_series α → puiseux_series α → puiseux_series α;
(** [pol_mul₂ add_coeff mul_coeff is_null_coeff p₁ p₂] *)
