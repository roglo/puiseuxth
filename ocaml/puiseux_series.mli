(* $Id: puiseux_series.mli,v 1.5 2013-04-06 22:53:57 deraugla Exp $ *)

type ps_monomial α = { coeff : α; power : Pnums.Q.t };
type puiseux_series α = { ps_monoms : list (ps_monomial α) };

value ps_add :
  (α → α → α) → (α → bool)
  → puiseux_series α → puiseux_series α → puiseux_series α;
(** [ps_add add_coeff is_null_coeff p₁ p₂] *)

value ps_mul :
  (α → α → α) → (α → α → α) → (α → bool)
  → puiseux_series α → puiseux_series α → puiseux_series α;
(** [ps_mul add_coeff mul_coeff is_null_coeff p₁ p₂] *)
