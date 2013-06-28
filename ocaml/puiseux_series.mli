(* $Id: puiseux_series.mli,v 1.39 2013-06-28 10:19:53 deraugla Exp $ *)

open Pnums;
open Field;
open Series;

type puiseux_series α =
  { ps_terms : series α;
    ps_valnum : I.t;
    ps_comden : I.t }
;
value ps_terms : puiseux_series α → series α;
value ps_valnum : puiseux_series α → I.t;
value ps_comden : puiseux_series α → I.t;

value ps_add :
  field α (ext α β) → puiseux_series α → puiseux_series α → puiseux_series α;
(** [ps_add fld p₁ p₂] *)

value ps_mul :
  field α (ext α β) → puiseux_series α → puiseux_series α → puiseux_series α;
(** [ps_mul fld p₁ p₂] *)

value series_head : (α → bool) → int → series α → option (int * α);

value valuation : field α β → puiseux_series α → option Q.t;
value valuation_coeff : field α β → puiseux_series α → α;

(* *)

type term α = { coeff : α; power : Q.t };
value coeff : term α → α;
value power : term α → Q.t;

value term_series_to_coeff_series : α → I.t → series (term α) → series α;
(** [term_series_to_coeff_series zero comden s *)
