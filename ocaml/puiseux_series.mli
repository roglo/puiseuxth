(* $Id: puiseux_series.mli,v 1.7 2013-05-22 17:23:05 deraugla Exp $ *)

type stream α = {hd : 'a; tl : Lazy.t (option (stream α))};

type ps_monomial α = { coeff : α; power : Pnums.Q.t };
type puiseux_series α = { ps_monoms : option (stream (ps_monomial α)) };
type old_ps α = { old_ps_mon : list (ps_monomial α) };

type comparison = [ Eq | Lt | Gt ];
value qcompare : Pnums.Q.t → Pnums.Q.t → comparison;

value ps_add :
  (α → α → α) → (α → bool)
  → old_ps α → old_ps α → old_ps α;
(** [ps_add add_coeff is_null_coeff p₁ p₂] *)

value ps_mul :
  (α → α → α) → (α → α → α) → (α → bool)
  → old_ps α → old_ps α → old_ps α;
(** [ps_mul add_coeff mul_coeff is_null_coeff p₁ p₂] *)
