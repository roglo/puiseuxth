(* $Id: puiseux_series.mli,v 1.18 2013-05-29 19:38:56 deraugla Exp $ *)

open Pnums;

type series α = [ Term of α and Lazy.t (series α) | End ];

type ps_monomial α = { coeff : α; power : Q.t };
type puiseux_series α =
  { ps_terms : series (ps_monomial α);
    ps_comden : I.t }
;

value coeff : ps_monomial α → α;
value power : ps_monomial α → Q.t;
value ps_terms : puiseux_series α → series (ps_monomial α);

type comparison = [ Eq | Lt | Gt ];
value qcompare : Q.t → Q.t → comparison;

value ps_add :
  (α → α → α) → puiseux_series α → puiseux_series α → puiseux_series α;
(** [ps_add add_coeff p₁ p₂] *)

value ps_mul :
  (α → α → α) → (α → α → α) → puiseux_series α → puiseux_series α →
    puiseux_series α;
(** [ps_mul add_coeff mul_coeff p₁ p₂] *)

(* *)

(* old version to be converted little by little: *)
type old_ps α = { old_ps_mon : list (ps_monomial α) };

value ps2ops : puiseux_series α → old_ps α;
value ops2ps : old_ps α → puiseux_series α;
