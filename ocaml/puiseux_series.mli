(* $Id: puiseux_series.mli,v 1.3 2013-04-06 12:07:53 deraugla Exp $ *)

type monomial₂ α = { coeff₂ : α; power₂ : Pnums.Q.t };
type puiseux_series α = { ps_monoms : list (monomial₂ α) };

value ps_add :
  (α → α → α) → (α → bool)
  → puiseux_series α → puiseux_series α → puiseux_series α;
(** [ps_add add_coeff is_null_coeff p₁ p₂] *)

value ps_mul :
  (α → α → α) → (α → α → α) → (α → bool)
  → puiseux_series α → puiseux_series α → puiseux_series α;
(** [ps_mul add_coeff mul_coeff is_null_coeff p₁ p₂] *)
