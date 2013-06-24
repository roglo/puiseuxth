(* $Id: puiseux_series.mli,v 1.29 2013-06-24 02:12:35 deraugla Exp $ *)

open Pnums;
open Field;
open Series;

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
  field α (ext α β) → puiseux_series α → puiseux_series α → puiseux_series α;
(** [ps_add fld p₁ p₂] *)

value ps_mul :
  field α (ext α β) → puiseux_series α → puiseux_series α → puiseux_series α;
(** [ps_mul fld p₁ p₂] *)

value series_head : (α → bool) → series (term α) → series (term α);

value valuation : field α β → puiseux_series α → option Q.t;
value valuation_coeff : field α β → puiseux_series α → α;

(* *)

(* old version to be converted little by little: *)
type old_ps α = { old_ps_mon : list (term α) };

value ps2ops : puiseux_series α → old_ps α;
value ops2ps : old_ps α → puiseux_series α;
