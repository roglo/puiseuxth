(* $Id: puiseux_series.mli,v 1.15 2013-05-24 14:56:47 deraugla Exp $ *)

open Pnums;

type series α = [ Term of α and Lazy.t (series α) | End ];

type ps_monomial α = { coeff : α; power : Q.t };
type puiseux_series α = { ps_terms : series (ps_monomial α) };

value coeff : ps_monomial α → α;
value power : ps_monomial α → Q.t;
value ps_terms : puiseux_series α → series (ps_monomial α);

(* old version to be converted little by little: *)
type old_ps α = { old_ps_mon : list (ps_monomial α) };

type comparison = [ Eq | Lt | Gt ];
value qcompare : Q.t → Q.t → comparison;

value ps_add : (α → α → α) → old_ps α → old_ps α → puiseux_series α;
(** [ps_add add_coeff p₁ p₂] *)

value ps_mul :
  (α → α → α) → (α → α → α) → (α → bool)
  → old_ps α → old_ps α → old_ps α;
(** [ps_mul add_coeff mul_coeff is_null_coeff p₁ p₂] *)

value ps2ops : puiseux_series α → old_ps α;
value ops2ps : old_ps α → puiseux_series α;
