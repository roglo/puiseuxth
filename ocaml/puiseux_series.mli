(* $Id: puiseux_series.mli,v 1.25 2013-06-23 14:10:56 deraugla Exp $ *)

open Pnums;

type series α = [ Term of α and Lazy.t (series α) | End ];

type term α = { coeff : α; power : Q.t };
value coeff : term α → α;
value power : term α → Q.t;

type puiseux_series α =
  { ps_terms : series (term α);
    ps_comden : I.t }
;
value ps_terms : puiseux_series α → series (term α);
value ps_comden : puiseux_series α → I.t;

value ps_add :
  (α → α → α) → puiseux_series α → puiseux_series α → puiseux_series α;
(** [ps_add add_coeff p₁ p₂] *)

value ps_mul :
  α → (α → bool) → (α → α → α) → (α → α → α) → puiseux_series α
  → puiseux_series α → puiseux_series α;
(** [ps_mul zero_coeff is_zero_coeff add_coeff mul_coeff p₁ p₂] *)

value series_nth_tl : int → series α → option (series α);
value series_map : (α → β) → series α → series β;
value series_head : (α → bool) → series (term α) → series (term α);

type comparison = [ Eq | Lt | Gt ];
value qcompare : Q.t → Q.t → comparison;

(* *)

(* old version to be converted little by little: *)
type old_ps α = { old_ps_mon : list (term α) };

value ps2ops : puiseux_series α → old_ps α;
value ops2ps : old_ps α → puiseux_series α;
