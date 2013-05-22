(* $Id: puiseux_series.mli,v 1.6 2013-05-22 15:34:55 deraugla Exp $ *)

type ps_monomial α = { coeff : α; power : Pnums.Q.t };
type puiseux_series α = { ps_monoms : list (ps_monomial α) };

type comparison = [ Eq | Lt | Gt ];
value qcompare : Pnums.Q.t → Pnums.Q.t → comparison;

value ps_add :
  (α → α → α) → (α → bool)
  → puiseux_series α → puiseux_series α → puiseux_series α;
(** [ps_add add_coeff is_null_coeff p₁ p₂] *)

value ps_mul :
  (α → α → α) → (α → α → α) → (α → bool)
  → puiseux_series α → puiseux_series α → puiseux_series α;
(** [ps_mul add_coeff mul_coeff is_null_coeff p₁ p₂] *)
