(* $Id: puiseux_series.mli,v 1.9 2013-05-22 21:17:45 deraugla Exp $ *)

type series α = [ Cons of α and Lazy.t (series α) | End ];

type ps_monomial α = { coeff : α; power : Pnums.Q.t };
type puiseux_series α = { ps_monoms : series (ps_monomial α) };
type old_ps α = { old_ps_mon : list (ps_monomial α) };

type comparison = [ Eq | Lt | Gt ];
value qcompare : Pnums.Q.t → Pnums.Q.t → comparison;

value ps_add :
  (α → α → α) → (α → bool)
  → old_ps α → old_ps α → puiseux_series α;
(** [ps_add add_coeff is_null_coeff p₁ p₂] *)

value ps_mul :
  (α → α → α) → (α → α → α) → (α → bool)
  → old_ps α → old_ps α → old_ps α;
(** [ps_mul add_coeff mul_coeff is_null_coeff p₁ p₂] *)

value ps2ops : puiseux_series α → old_ps α;
